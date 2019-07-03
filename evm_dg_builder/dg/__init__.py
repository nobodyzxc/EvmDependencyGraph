import networkx as nx
from Crypto.Hash import keccak
import random
from itertools import product, chain

flatten = lambda it: list(chain.from_iterable(it))

indirects = ('MSTORE', 'SSTORE', 'MLOAD', 'SLOAD',
        'CALLVALUE', 'CALLER', 'CALLDATALOAD')

def sha3(code):
    keccak_hash = keccak.new(digest_bits=256)
    keccak_hash.update(code)
    return keccak_hash.hexdigest()

def bit_not(n, numbits=256):
    return (1 << numbits) - 1 - n

def randColor():
    r = lambda: random.randint(0,255)
    return '#%02X%02X%02X' % (r(),r(),r())

def opcode_of(self, pc):
    if isinstance(pc, list):
        return [self.cfg.instructions_from_addr[p] for p in pc]
    return self.cfg.instructions_from_addr[pc]

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
        self.mloads = {} # key ins, val [pc]
        self.sloads = {} # key ins, val [pc]
        self.memory = {} # key addr, val [ins]
        self.storage = {} # key addr, val [ins]

        self.op_addr = {} # if const addr or [inst] depend on
        self.addr_dep = {}

        # for op pcs
        self.visited = set()
        self.evaled = set()

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

        for lpc in self.addr_dep:
            for spc in self.addr_dep[lpc]:
                g.add_edge(self.name_of(lpc),
                        self.name_of(spc),
                        style='dashed')
        return g

    def eval_op(self, op, ct):
        """
            return (potential constant values, abstract values)
        """
        # self.graph[addr] == Node
        # node.argNodes = set() # set of (addr, addr, ...)
        if op.pc in self.visited:
            return [None], set([op.pc]) # '#={}'.format(op.pc)

        #if ct > 300: return [], ['...exceed the recursion limit']

        ev_addr = lambda addr: self.eval_op(self.cfg.instructions_from_addr[addr], ct + 1)
        lzip = lambda *e: list(zip(*e))

        if not op:
            raise Exception("Op == None")
        elif op.name.startswith("PUSH"):
            return [int(op.operand)], set()
        else:
            self.visited.add(op.pc)
            potential_consts, depended_absts = [], set()
            for args in self.graph[op.pc].argNodes:
                #a = [ev_addr(arg) for arg in args]
                #b = lzip(*[ev_addr(arg) for arg in args])
                #print('prev ->', a)
                #print('next ->', b)
                consts, absts = lzip(*[ev_addr(arg) for arg in args]) if args else ([], [])
                val = None
                #print('consts:', consts)
                #print('absts:', absts)
                for eargs in product(*consts):
                    if None in eargs: continue
                    #print('op: {} args: {}'.format(op.name, args))
                    #print('op:', op.name, 'args ->', eargs)
                    #print('{} {} args -> {}'.format(hex(op.pc), op.name, eargs))
                    if op.name == 'EXP':
                        val = eargs[0] ** eargs[1]
                    elif op.name == 'MUL':
                        val = eargs[0] * eargs[1]
                    elif op.name == 'ISZERO': # simple not
                        val = 1 if eargs[0] == 0 else 0
                    elif op.name == 'NOT': # bit wise not
                        val = bit_not(eargs[0])
                    elif op.name == 'ADD':
                        val = sum(eargs)
                    elif op.name == 'SUB':
                        val = eargs[0] - eargs[1]
                    elif op.name == 'AND':
                        val = eargs[0] & eargs[1]
                    elif op.name == 'DIV':
                        val = eargs[0] // eargs[1]
                    elif op.name == 'EQ':
                        val = 1 if eargs[0] == eargs[1] else 0
                    elif op.name == 'SHA3':
                        depended_absts.update([x for x in range(eargs[0], eargs[1])])
                    #    val = sha3(bytes(mem[eargs[0]:eargs[1]]))
                    elif op.name in indirects:
                        depended_absts.add(op.pc)
                    else:
                        raise Exception("eval_op: need support {}".format(op.name))
                    if val: potential_consts.append(val)
                absts = flatten(absts)
#                print("""
#extend: {}
#                """.format(absts))
                depended_absts.update(absts)

            self.visited.remove(op.pc)
            if not potential_consts: potential_consts = [None]
            return potential_consts, depended_absts

    def findBlock(self, pc):
        for bb_pc in self.cfg.basic_blocks_from_addr:
            bb = self.cfg.basic_blocks_from_addr[bb_pc]
            if pc >= bb.start.pc and pc <= bb.end.pc:
                return bb

    def eval_addrs(self):

        self.inst2block = {} # inst.pc : basicblock
        self.block2inst_mem = {} # basicblock : [inst.pc]
        self.block2inst_sto = {} # basicblock : [inst.pc]
        self.inst_cons_addr = {}
        self.inst_abst_addr = {}
        self.inst_cons_val = {}
        self.inst_abst_val = {}
"""
read op:

    SHA3     s[0] .. (s[0] + s[1] - 1)
    MLOAD    s[0] .. (s[0] + 31)
    CREATE   s[1] .. (s[1] + s[2] - 1)
    CALL     s[3] .. (s[3] + s[4] - 1)
    RETURN   s[0] .. (s[0] + s[1] - 1)

    SLOAD    s[0]
    SELFDESTRUCT omit

write op:

    MSTORE   s[0] .. (s[0] + 31)

    SSTORE   s[0]

"""

        for pc in self.mstores:
            bb = self.findBlock(pc)
            self.inst2block[pc] = bb
            self.block2inst_mem.setdefault(bb, set()).add(pc)
        for pc in self.mloads:
            bb = self.findBlock(pc)
            self.inst2block[pc] = bb
            self.block2inst_mem.setdefault(bb, set()).add(pc)
        for pc in self.sstores:
            bb = self.findBlock(pc)
            self.inst2block[pc] = bb
            self.block2inst_sto.setdefault(bb, set()).add(pc)
        for pc in self.sloads:
            bb = self.findBlock(pc)
            self.inst2block[pc] = bb
            self.block2inst_sto.setdefault(bb, set()).add(pc)

        print('output:', self.inst2block)

        insts = self.cfg.instructions_from_addr

        print("# MSTORE")
        for pc in self.mstores:
            for (addr, val) in self.mstores[pc]:
                addr_cons, addr_abs = self.eval_op(addr, 0)
                val_cons, val_abs = self.eval_op(val, 0)
                if not addr_abs and not val_abs: self.evaled.add(pc)
                self.inst_cons_addr.setdefault(pc, set()).update(addr_cons)
                self.inst_abst_addr.setdefault(pc, set()).update(addr_abs)
                self.inst_cons_val.setdefault(pc, set()).update(val_cons)
                self.inst_abst_val.setdefault(pc, set()).update(val_abs)
#                print("""
#MSTROE@{}
#
#    addr:
#      - cons: {}
#      - abst: {}
#    vals:
#      - cons: {}
#      - abst: {}
#                """.format(pc, addr_cons, addr_abs, val_cons, val_abs))

        print("# MLOAD")
        for pc in self.mloads:
            for addr in self.mloads[pc]:
                addr_cons, addr_abs = self.eval_op(addr, 0)
                if not addr_abs: self.evaled.add(pc)
                self.inst_cons_addr.setdefault(pc, set()).update(addr_cons)
                self.inst_abst_addr.setdefault(pc, set()).update(addr_abs)
#                print("""
#MLOAD@{}
#
#    addr:
#      - cons: {}
#      - abst: {}
#                """.format(pc, addr_cons, addr_abs))


        print("# SSTORE")
        for pc in self.sstores:
            for (addr, val) in self.sstores[pc]:
                addr_cons, addr_abs = self.eval_op(addr, 0)
                val_cons, val_abs = self.eval_op(val, 0)
                if not addr_abs and not val_abs: self.evaled.add(pc)
                self.inst_cons_addr.setdefault(pc, set()).update(addr_cons)
                self.inst_abst_addr.setdefault(pc, set()).update(addr_abs)
                self.inst_cons_val.setdefault(pc, set()).update(val_cons)
                self.inst_abst_val.setdefault(pc, set()).update(val_abs)
#                print("""
#SSTROE@{}
#
#    addr:
#      - cons: {}
#      - abst: {}
#    vals:
#      - cons: {}
#      - abst: {}
#                """.format(pc, addr_cons, addr_abs, val_cons, val_abs))


        print("# SLOAD")
        for pc in self.sloads:
            for addr in self.sloads[pc]:
                addr_cons, addr_abs = self.eval_op(addr, 0)
                if not addr_abs: self.evaled.add(pc)
                self.inst_cons_addr.setdefault(pc, set()).update(addr_cons)
                self.inst_abst_addr.setdefault(pc, set()).update(addr_abs)
#                print("""
#SLOAD@{}
#
#    addr:
#      - cons: {}
#      - abst: {}
#                """.format(pc, addr_cons, addr_abs))

        #print('cons addr:', self.inst_cons_addr)
        #print('abst addr:', self.inst_abst_addr)
        #print('cons val:', self.inst_cons_val)
        #print('abst val:', self.inst_abst_val)

    def build_dependency(self):
        self.eval_addrs()
        self.build_addr_dependency(self.mstores, self.mloads, self.block2inst_mem)
        self.build_addr_dependency(self.sstores, self.sloads, self.block2inst_sto)

    def build_addr_dependency(self, stores, loads, b2i):

        cons_stores = []
        visited_stores = set()
        for pc in stores:
            if self.inst_cons_addr[pc] and self.inst_cons_val[pc]:
                cons_stores.append(pc)
                visited_stores.add(pc)

        while cons_stores:

            while cons_stores:
                pc = cons_stores.pop()
                self.cfg_depend_dfs(pc, self.inst2block[pc], b2i, loads, set())

            for pc in stores:
                if pc not in visited_stores \
                        and self.inst_cons_addr[pc] \
                        and self.inst_cons_val[pc]:
                    cons_stores.append(pc)
                    visited_stores.add(pc)

        print(set(stores.keys()))
        print(visited_stores)
        #print(set(stores.keys()).difference(visited_stores))


    def cfg_depend_dfs(self, spc, curb, b2i, loads, visited):

        saddrs = self.inst_cons_addr[spc]
        inst_of = self.cfg.instructions_from_addr

        if curb in visited: return []
        else: visited.add(curb)

        for pc in b2i.get(curb, []):
            if pc in loads:
                laddrs = self.inst_cons_addr[pc]
                laddrs_a = self.inst_abst_addr[pc]
                if laddrs:
                    if laddrs.intersection(saddrs):
                        self.addr_dep.setdefault(pc, set()).add(spc)
                else:
                    if all([self.inst_abst_addr[dr] for dr in aaddrs_a] \
                            + [self.inst_abst_addr[dr] for dr in aaddrs_a]):
                        # re_eval
                        pass

        #for abst_pc in
        for bb in curb.all_outgoing_basic_blocks:
            self.cfg_depend_dfs(spc, bb, b2i, loads, visited)

        visited.remove(curb)
