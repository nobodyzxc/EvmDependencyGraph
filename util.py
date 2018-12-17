import os, re
import shlex
import subprocess

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
