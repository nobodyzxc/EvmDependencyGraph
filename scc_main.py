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

    print(len(cfg.basic_blocks))

    # for inst in cfg.asm:
    #     print(inst)
    scc_graph = SCCGraph(cfg)
    sym_exec_scc_graph(scc_graph, bytecode)


    htmlname = 'scc_' + filename[:filename.find('.')] + '_' + filename[filename.find(':') + 1:]+ '.html'

    CFGDotExporter(scc_graph).export(htmlname)
