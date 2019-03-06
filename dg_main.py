from util import *
from scc import SCCGraph
from evm_dg_builder.cfg import CFG
from argparse import ArgumentParser
from sym_exec import sym_exec_scc_graph
from exporter import DGDotExporter

parser = ArgumentParser()
parser.add_argument("src", help="source file name")

args = parser.parse_args()

contracts = compile_contracts(args.src)

for filename, bytecode in contracts:

    print(filename, ':')

    cfg = CFG(bytecode)
    DGDotExporter(cfg.dg).\
    export(filename[:filename.find('.')] + '.html')
    for ins in cfg.instructions:
        print(ins.pc, ins.name)
    '''
    dotfile = cfg.output_to_dot(filename)
    output_graph(dotfile, filename[:filename.find('.')])
    '''
