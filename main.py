from util import *
from scc import SCCTree
from evm_cfg_builder.cfg import CFG
from argparse import ArgumentParser

parser = ArgumentParser()
parser.add_argument("src", help="source file name")

args = parser.parse_args()

contracts = compile_contracts(args.src)

for filename, bytecode in contracts:

    cfg = CFG(bytecode)
    dotfile = cfg.output_to_dot(filename)
    output_graph(dotfile, filename[:filename.find('.')])

    scc_tree = SCCTree(cfg)
    print(filename, ':')
    print(scc_tree.sccs)
