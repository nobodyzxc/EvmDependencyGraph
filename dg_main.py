from util import *
from scc import SCCGraph
from evm_dg_builder.cfg import CFG
from argparse import ArgumentParser
from sym_exec import sym_exec_scc_graph
from exporter import DGDotExporter

parser = ArgumentParser()
parser.add_argument("src", help="source file name")
parser.add_argument( "-b",   "--bytecode",
                    help="read bytecode in source instead of solidity file.",
                    action="store_true")

args = parser.parse_args()

if args.bytecode:

    filename = args.src

    with open(filename, 'r') as f:

        print(filename, ':')
        bytecode = f.read()
        cfg = CFG(bytecode)
        DGDotExporter(cfg.dg).\
        export(filename[:filename.find('.')] + '.html')
        for ins in cfg.instructions:
            print(ins.pc, ins.name)

else:
    contracts = compile_contracts(args.src)

    for filename, bytecode in contracts:

        print(filename)

        cfg = CFG(bytecode)
        htmlname = filename[:filename.find('.')] + '_' + filename[filename.find(':') + 1:]+ '.html'
        print('export as', htmlname)
        DGDotExporter(cfg.dg).\
                export(htmlname)
        #for ins in cfg.instructions:
        #    print(ins.pc, ins.name)
        '''
        dotfile = cfg.output_to_dot(filename)
        output_graph(dotfile, filename[:filename.find('.')])
        '''
        #while True:
        #    #print(cfg.dg.graph)
        #    pc = int(input('input pc> '))
        #    if pc == -1: break
        #    print(cfg.dg.graph[pc].argNodes)
