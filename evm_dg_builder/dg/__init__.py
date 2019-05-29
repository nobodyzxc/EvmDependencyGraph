import networkx as nx
import random
from itertools import product

def randColor():
    r = lambda: random.randint(0,255)
    return '#%02X%02X%02X' % (r(),r(),r())

class Node(object):

    def __init__(self, pc, opcode):
        self.pc = pc
        self.name = opcode
        self.toNodes = set()  # set of addr
        self.argNodes = set() # set of (addr, addr, ...)

    def add_dependency(self, insts):
        addrs = [i.pc if i else -1 for i in insts]
        self.toNodes.update(addrs)
        self.argNodes.add(tuple(addrs))

class DG(object):

    def __init__(self, cfg):
        self.graph = {}
        self.cfg = cfg
        self.color = dict()
        self.clr = dict()

        # record mem, sto here
        self.mstores = {} # key ins, val [(addr, value)]
        self.sstores = {} # key ins, val [(addr, value)]
        self.mloads = {} # key ins, val [addr]
        self.sloads = {} # key ins, val [addr]
        self.memory = {} # key addr, val [ins]
        self.storage = {} # key addr, val [ins]

        # visited op
        self.visited = set()

    def __getitem__(self, key):
        return self.graph[key];

    def __iter__(self):
        for k in self.graph:
            yield k

    def name_of(self, addr):
        return hex(addr) + ' ' + self.graph[addr].name

    @property
    def instructions(self):
        return self.cfg.insts

    def add_edges(self, ins, insts):

        # build nodes
        for i in insts + [ins]:
            if not i:
                pass
                # print("unknown")
            elif i.pc not in self.graph:
                self.graph[i.pc] = Node(i.pc, i.name)

        node = self.graph[ins.pc]
        node.add_dependency(insts)
        color = randColor()
        for i in insts:
            self.color[(ins.pc, i.pc)] = color
        self.clr[((ins.pc, tuple([i.pc if i else -1 for i in insts])))] = color

    def nx_graph(self):

        #g = nx.DiGraph()
        g = nx.MultiDiGraph()

        g.add_nodes_from(self.name_of(pc) for pc in self.graph)

        #for pc in self.graph:
        #    for dp in self.graph[pc].toNodes:
        #        g.add_edge(hex(pc), hex(dp), color=self.color[(pc, dp)])

        for pc in self.graph:
            for arg in self.graph[pc].argNodes:
                for dp in arg:
                    #if pc == 1260: input("{}, {}, {}".format(arg, dp, self.clr[(pc, arg)]))
                    g.add_edge(self.name_of(pc),
                                self.name_of(dp),
                                color=self.clr[(pc, arg)])


        for bb in self.cfg.basic_blocks:
            #if len(bb.instructions) >= 2:
            #    g.add_edge(hex(bb.start.pc), hex(bb.instructions[1].pc), style='dashed')
            for obb in bb.all_outgoing_basic_blocks:
                if obb.start.pc not in self.graph:
                    self.graph[obb.start.pc] = Node(obb.start.pc, obb.start.name)
                if bb.end.pc not in self.graph:
                    self.graph[bb.end.pc] = Node(bb.end.pc, bb.end.name)
                g.add_edge(self.name_of(bb.end.pc),
                        self.name_of(obb.start.pc),
                        style='dotted')

        return g

    def eval_op(self, op, ct):
        # self.graph[addr] == Node
        # node.argNodes = set() # set of (addr, addr, ...)
        if op.pc in self.visited:
            return ['#=' + str(hex(op.pc))]


        if ct > 300: return ['...unknown']
        insts = self.cfg.instructions_from_addr
        ev_addr = lambda addr: self.eval_op(insts[addr], ct + 1)
        if not op:
            return ['None']
        elif op.name.startswith("PUSH"):
            return [str(op.operand)]
            #return str(op.operand)
        else:
            self.visited.add(op.pc)
            rtns = []
            for args in self.graph[op.pc].argNodes:
                for eargs in product(*list(map(ev_addr, args))):
                    if all(map(lambda s:s.isdigit(), eargs)):
                        if op.name == 'EXP':
                            a, b = map(int, eargs)
                            return str(a ** b)
                        elif op.name == 'ISZERO':
                            a = int(eargs[0])
                            arglist = str(0 if a else 1)
                        elif op.name == 'ADD':
                            arglist = str(sum(map(int, eargs)))
                        elif op.name == 'SUB':
                            a, b = map(int, eargs)
                            arglist = str(a - b)
                        elif op.name == 'AND':
                            a, b = map(int, eargs)
                            arglist = str(a & b)
                        elif op.name == 'DIV':
                            a, b = map(int, eargs)
                            arglist = str(a // b)
                        elif op.name == 'EQ':
                            a, b = map(int, eargs)
                            arglist = str(1 if a == b else 0)
                        else:
                            arglist = '{}[{}]({})'.format(op.name, hex(op.pc), ','.join(eargs))
                        #    print('>>=', arglist)
                    else:
                        arglist = ','.join(eargs)
                        if '...' in arglist:
                            arglist = 'bomb@' + str(op.pc)
                        else:
                            arglist = '{}[{}]({})'.format(op.name, hex(op.pc), arglist)
                    rtns.append(arglist)
            self.visited.remove(op.pc)
            return rtns

    def eval_addrs(self):
        insts = self.cfg.instructions_from_addr
        print("# MSTORE")
        for pc in self.mstores:
            for (addr, val) in self.mstores[pc]:
                #print("{:4d} {}: mem[{:4d} {}] = {:4d} {}".format(
                #    pc, insts[pc].name, addr.pc, addr.name, val.pc, val.name))
                ars, vls = self.eval_op(addr, 0), self.eval_op(val, 0)
                for a in ars:
                    for v in vls:
                        print("{:6s} {}: mem[{}] = {}".format(
                            hex(pc), insts[pc].name, a, v))
                #self.memory.setdefault(self.eval_addr(addr), []).append(val)

        print("# MLOAD")
        for pc in self.mloads:
            for addr in self.mloads[pc]:
                ars = self.eval_op(addr, 0)
                #self.storage.setdefault(self.eval_addr(addr), []).append(val)
                for a in ars:
                    print("{:6s} {}: mem[{}]".format(
                            hex(pc), insts[pc].name, a))


        print("# SSTORE")
        for pc in self.sstores:
            for (addr, val) in self.sstores[pc]:
                ars, vls = self.eval_op(addr, 0), self.eval_op(val, 0)
                #self.storage.setdefault(self.eval_addr(addr), []).append(val)
                for a in ars:
                    for v in vls:
                        print("{:6s} {}: sto[{}] = {}".format(
                            hex(pc), insts[pc].name, a, v))

        print("# SLOAD")
        for pc in self.sloads:
            for addr in self.sloads[pc]:
                ars = self.eval_op(addr, 0)
                #self.storage.setdefault(self.eval_addr(addr), []).append(val)
                for a in ars:
                    print("{:6s} {}: sto[{}]".format(
                            hex(pc), insts[pc].name, a))

