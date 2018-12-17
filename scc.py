class SCCTree():
    def __init__(self, cfg):

        self.sccs = []
        self.scc_set = {}
        self.finish = []

        self.visited = set()
        self.find_finish(cfg)

        self.visited.clear()
        self.find_scc(cfg)

        self.set_collapsing()
        self.cfg_root = cfg.basic_blocks_from_addr[0x0]
        self.root = self.scc_set[self.cfg_root]

        self.visited.clear()
        self.build_tree(cfg, self.cfg_root)

    def dfs(self, cfg, cur, edgeOf, callback):
        self.visited.add(cur)
        for bb in edgeOf(cur):
            if bb not in self.visited:
                self.dfs(cfg, bb, edgeOf, callback)
        callback(cur)

    def find_finish(self, cfg):
        for bb in cfg.basic_blocks:
            if bb not in self.visited:
                self.dfs(cfg, bb,
                    lambda bb: bb.all_outgoing_basic_blocks,
                    lambda bb: self.finish.append(bb))

    def find_scc(self, cfg):
        for bb in self.finish[-1::-1]:
            if bb not in self.visited:
                scc = SCC(bb)
                self.sccs.append(scc)
                self.dfs(cfg, bb,
                    lambda bb: bb.all_incoming_basic_blocks,
                    lambda bb: scc.add_vertex(bb))

    def set_collapsing(self):
        for scc in self.sccs:
            for vertex in scc.vertices:
                self.scc_set[vertex] = scc

    def build_tree(self, cfg, cur):
        self.visited.add(cur)
        cur_scc = scc_set[cur]
        for bb in cur.all_outgoing_basic_blocks:
            if bb not in self.visited and scc_set[bb] != cur_scc:
                cur_scc.add_outing_scc(scc_set[bb])
                build_tree(self, cfg, bb)

class SCC():
    def __init__(self, root):
        self.root = root
        self.vertices = []
        self.all_outgoing_sccs = set()
    def add_vertex(self, bb):
        self.vertices.append(bb)
    def add_outing_scc(self, scc):
        self.all_outgoing_sccs.add(scc)
