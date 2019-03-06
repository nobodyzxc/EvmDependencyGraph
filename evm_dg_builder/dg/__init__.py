import networkx as nx
class Node(object):

    def __init__(self, pc, opcode):
        self.pc = pc
        self.name = opcode
        self.toNodes = set()  # set of addr
        self.argNodes = set() # set of (addr, addr)

    def add_dependency(self, insts):
        addrs = [i.pc if i else -1 for i in insts]
        self.toNodes.update(addrs)
        self.argNodes.add(tuple(addrs))

class DG(object):

    def __init__(self, cfg):
        self.graph = {}
        self.cfg = cfg

    def __getitem__(self, key):
        return self.graph[key];

    def __iter__(self):
        for k in self.graph:
            yield k

    @property
    def instructions(self):
        return self.cfg.insts

    def add_edges(self, ins, insts):
        for i in insts + [ins]:
            if not i:
                pass
                # print("unknown")
            elif i.pc not in self.graph:
                self.graph[i.pc] = Node(i.pc, i.name)

        node = self.graph[ins.pc]
        node.add_dependency(insts)

    def nx_graph(self):

        g = nx.DiGraph()

        g.add_nodes_from(hex(pc) for pc in self.graph)

        for pc in self.graph:
            g.add_edges_from((hex(pc), hex(dp)) \
                for dp in self.graph[pc].toNodes)

        return g
