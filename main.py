from util import *
from scc import SCCGraph
from evm_cfg_builder.cfg import CFG
from argparse import ArgumentParser
from sym_exec import sym_exec_scc_graph
from exporter import CFGDotExporter

parser = ArgumentParser()
parser.add_argument("src", help="source file name")

args = parser.parse_args()

contracts = compile_contracts(args.src)

for filename, bytecode in contracts:

    print(filename, ':')

    cfg = CFG(bytecode)

    '''
    dotfile = cfg.output_to_dot(filename)
    output_graph(dotfile, filename[:filename.find('.')])
    '''

    scc_graph = SCCGraph(cfg)
    sym_exec_scc_graph(scc_graph, bytecode)
    CFGDotExporter(scc_graph).export(filename[:filename.find('.')] + '.html')
