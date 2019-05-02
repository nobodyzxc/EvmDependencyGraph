import networkx as nx
import random

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
