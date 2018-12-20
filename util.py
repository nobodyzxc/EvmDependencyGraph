import os, re
import shlex
import subprocess
import six
from z3 import *
from z3.z3util import get_vars

def cmd_exists(cmd):
    return subprocess.call("type " + cmd, shell=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE) == 0

def run_command(cmd):
    FNULL = open(os.devnull, 'w')
    solc_p = subprocess.Popen(shlex.split(cmd), stdout=subprocess.PIPE, stderr=FNULL)
    return solc_p.communicate()[0].decode('utf-8', 'strict')

def compile_contracts(filename):

    if not cmd_exists("solc"): print('please install solc'), exit(1)

    out = run_command("solc --bin-runtime %s" % (filename))

    libs = re.findall(r"_+(.*?)_+", out)
    libs = set(libs)

    if libs: print('need link libraries'), exit(1)

    binary_regex = r"\n======= (.*?) =======\nBinary of the runtime part: \n(.*?)\n"
    contracts = re.findall(binary_regex, out)
    contracts = [contract for contract in contracts if contract[1]]

    if not contracts: print("compilation failed"), exit(1)

    return contracts

def output_graph(dotfile, filename):
    subprocess.call("dot -Tsvg %s -o %s.svg" % \
            (dotfile, filename), shell=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    subprocess.call("rm {}".format(dotfile), shell=True)

def ceil32(x):
    return x if x % 32 == 0 else x + 32 - (x % 32)

def isSymbolic(value):
    return not isinstance(value, six.integer_types)

def isReal(value):
    return isinstance(value, six.integer_types)

def isAllReal(*args):
    for element in args:
        if isSymbolic(element):
            return False
    return True

def to_symbolic(number):
    if isReal(number):
        return BitVecVal(number, 256)
    return number

def to_unsigned(number):
    if number < 0:
        return number + 2**256
    return number

def to_signed(number):
    if number > 2**(256 - 1):
        return (2**(256) - number) * (-1)
    else:
        return number

def check_sat(solver, pop_if_exception=True):
    try:
        ret = solver.check()
        if ret == unknown:
            raise Z3Exception(solver.reason_unknown())
    except Exception as e:
        if pop_if_exception:
            solver.pop()
        raise e
    return ret


