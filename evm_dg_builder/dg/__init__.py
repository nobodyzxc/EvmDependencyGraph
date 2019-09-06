import networkx as nx
from Crypto.Hash import keccak
import random
from itertools import product, chain

flatten = lambda it: list(chain.from_iterable(it))

hl = lambda s: sorted([hex(e) for e in s])

indirects = ('MSTORE', 'SSTORE', 'MLOAD', 'SLOAD', 'SHA3')


indreads = ('SLOAD', 'MLOAD', 'SHA3')
indwrites = ('SSTORE', 'MSTORE')

externals = ('ADDRESS', 'TIMESTAMP', 'NUMBER', 'CALLDATASIZE', 'RETURNDATASIZE', 'CALLER', 'CALLVALUE', 'CALLDATALOAD', 'CALL', 'RETURN'
,'CREATE'
,'MSIZE'
,'BALANCE'
,'ORIGIN'
,'CALLDATACOPY'
,'CODESIZE'
,'EXTCODESIZE'
,'CODECOPY'
,'EXTCODECOPY'
,'RETURNDATACOPY'
,'GASPRICE'
,'BLOCKHASH'
,'COINBASE'
,'DIFFICULTY'
,'GASLIMIT')





def sha3(code):
    keccak_hash = keccak.new(digest_bits=256)
    keccak_hash.update(code)
    #keccak_hash.update('hello world'.encode('UTF-8'))
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

def overlap(write_cons, write_off, read_cons, read_off):
    for r in product(read_cons, read_off):
        for w in product(write_cons, write_off):
            (lb, lo), (hb, ho) = sorted([r, w])
            if hb < lb + lo:
                return True
    return False

class DG(object):

    def __init__(self, cfg):
        self.graph = {}
        self.cfg = cfg
        self.color = dict()
        self.clr = dict()

        # record mem, sto here
        self.mwrites = {} # key ins, val [(addr, value)]
        self.swrites = {} # key ins, val [(addr, value)]
        self.mreads = {} # key ins, val [pc]
        self.sreads = {} # key ins, val [pc]

        self.memory = {} # key addr, val [ins]
        self.storage = {} # key addr, val [ins]

        self.op_addr = {} # if const addr or [inst] depend on
        self.rw_dep = {}

        # for op pcs
        self.visited = set()
        self.evaled = set()
        # instruction of pc

    def __getitem__(self, key):
        return self.graph[key];

    def __iter__(self):
        for k in self.graph:
            yield k

    def name_of(self, addr):
        if addr in self.graph:
            return hex(addr) + ' ' + self.graph[addr].name
        else: return hex(addr)

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
            if ins and i:
                self.color[(ins.pc, i.pc)] = color
        self.clr[((ins.pc, tuple([i.pc if i else -1 for i in insts])))] = color

    def nx_graph(self):

        g = nx.MultiDiGraph()

        g.add_nodes_from(self.name_of(pc) for pc in self.graph)

        for pc in self.graph:
            for arg in self.graph[pc].argNodes:
                for dp in arg:
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

        for lpc in self.rw_dep:
            for spc in self.rw_dep[lpc]:
                g.add_edge(self.name_of(lpc),
                        self.name_of(spc),
                        style='dashed')
        return g

    def record_ins(self, ins, args):

        """
        write op:

            MSTORE   s[0] .. (s[0] + 31)

            SSTORE   s[0]

        read op:

            MLOAD    s[0] .. (s[0] + 31)
            SHA3     s[0] .. (s[0] + s[1] - 1)
            CREATE   s[1] .. (s[1] + s[2] - 1)
            CALL     s[3] .. (s[3] + s[4] - 1)
            RETURN   s[0] .. (s[0] + s[1] - 1)

            SLOAD    s[0]
            SELFDESTRUCT omit

        """
        if not all(args): return

        if ins.name == 'MSTORE':
            addr, val = args[0], args[1]
            self.mwrites.setdefault(ins.pc, []).append((addr, 32, val))

        if ins.name == 'SSTORE':
            addr, val = args[0], args[1]
            self.swrites.setdefault(ins.pc, []).append((addr, 1, val))

        if ins.name == 'MLOAD':
            addr = args[0]
            self.mreads.setdefault(ins.pc, []).append((addr, 32))
        elif ins.name == 'SHA3':
            beg, offset = args[:2]
            self.mreads.setdefault(ins.pc, []).append((beg, offset))
        elif ins.name == 'CREATE':
            beg, offset = args[1:3]
            self.mreads.setdefault(ins.pc, []).append((beg, offset))
        elif ins.name == 'CALL':
            beg, offset = args[3:5]
            self.mreads.setdefault(ins.pc, []).append((beg, offset))
        elif ins.name == 'RETURN':
            beg, offset = args[0:2]
            self.mreads.setdefault(ins.pc, []).append((beg, offset))
        elif ins.name == 'SLOAD':
            addr = args[0]
            self.sreads.setdefault(ins.pc, []).append((addr, 1))

    def re_eval_op(self, op, visited, ct):
        """
            return (potential constant values, abstract values)
        """
        if isinstance(op, int):
            return [op], set()

        if op.pc in visited:
            return [], set([op.pc]) # '#={}'.format(op.pc) # [None]

        #if ct > 300: return [], ['...exceed the recursion limit']

        #ev_addr = lambda addr: self.eval_op( \
        ev_addr = lambda addr: self.re_eval_op( \
                self.cfg.instructions_from_addr[addr], visited, ct + 1)

        lzip = lambda *e: list(zip(*e))

        if not op:
            raise Exception("Op == None")
        elif op.name.startswith("PUSH"):
            return [int(op.operand)], set()
        else:
            visited.add(op.pc)
            potential_consts, depended_absts = [], set()
            for args in self.graph[op.pc].argNodes:
                if -1 in args: continue # patch
                consts, absts = lzip(*[ev_addr(arg) for arg in args]) \
                                            if args else ([], [])
                val = None
                for eargs in product(*consts):
                    if None in eargs: continue
                    if op.name == 'EXP':
                        val = pow(eargs[0], eargs[1], 256)
                    elif op.name == 'MUL':
                        val = eargs[0] * eargs[1]
                    elif op.name == 'ISZERO': # simple not
                        val = 1 if eargs[0] == 0 else 0
                    elif op.name == 'NOT': # bit wise not
                        val = bit_not(eargs[0])
                    elif op.name == 'ADD':
                        val = (eargs[0] + eargs[1]) % (2 ** 256)
                    elif op.name == 'SUB':
                        val = (eargs[0] - eargs[1]) % (2 ** 256)
                    elif op.name == 'AND':
                        val = eargs[0] & eargs[1]
                    elif op.name == 'OR':
                        val = eargs[0] | eargs[1]
                    elif op.name == 'DIV':
                        val = eargs[0] // eargs[1]
                    elif op.name == 'EQ':
                        val = 1 if eargs[0] == eargs[1] else 0
                    #elif op.name == 'SHA3':
                    #    # μ′s[0]≡Keccak(μm[μs[0]...(μs[0] +μs[1]−1)])
                    #    raise Exception("re-eval_op: need support {}".format(op.name))
                    elif op.name in externals:
                        pass
                    elif op.name in indreads:
                        try:
                            potential_consts.extend(self.inst_cons_val.get(op.pc, []))
                        except Exception as e:
                            print('exception at', op.name)
                    else:
                        raise Exception("re-eval_op: need support {}".format(op.name))
                    if val and val < 0: print(op, op.name, op.pc, eargs), exit(0)
                    if type(val) == float: print(op, op.name, op.pc, eargs), exit(0)
                    if val != None: potential_consts.append(val)
                absts = flatten(absts)
                depended_absts.update(absts)

            visited.remove(op.pc)

            if not potential_consts and not depended_absts:
                print("{}@{} is empty", op.name, op.pc)#, exit(0)
                depended_absts.add(op.pc) # TODO

            return potential_consts, depended_absts


    def eval_op(self, op, visited, ct):
        """
            return (potential constant values, abstract values)
        """
        if isinstance(op, int):
            return [op], set()
        # self.graph[addr] == Node
        # node.argNodes = set() # set of (addr, addr, ...)
        if op.pc in visited:
            return [], set([op.pc]) # '#={}'.format(op.pc) # [None]

        #if ct > 300: return [], ['...exceed the recursion limit']

        ev_addr = lambda addr: self.eval_op( \
                self.cfg.instructions_from_addr[addr], visited, ct + 1)

        lzip = lambda *e: list(zip(*e))

        if not op:
            raise Exception("Op == None")
        elif op.name.startswith("PUSH"):
            return [int(op.operand)], set()
        else:
            visited.add(op.pc)
            potential_consts, depended_absts = [], set()
            for args in self.graph[op.pc].argNodes:
                if -1 in args: continue # patch
                consts, absts = lzip(*[ev_addr(arg) for arg in args]) if args else ([], [])
                val = None
                for eargs in product(*consts):
                    if None in eargs: continue
                    if op.name == 'EXP':
                        print(eargs[0], eargs[1])
                        val = pow(eargs[0], eargs[1], 256)
                    elif op.name == 'MUL':
                        val = eargs[0] * eargs[1]
                    elif op.name == 'ISZERO': # simple not
                        val = 1 if eargs[0] == 0 else 0
                    elif op.name == 'NOT': # bit wise not
                        val = bit_not(eargs[0])
                    elif op.name == 'ADD':
                        val = (eargs[0] + eargs[1]) % (2 ** 256)
                    elif op.name == 'SUB':
                        val = (eargs[0] - eargs[1]) % (2 ** 256)
                    elif op.name == 'AND':
                        val = eargs[0] & eargs[1]
                    elif op.name == 'OR':
                        val = eargs[0] | eargs[1]
                    elif op.name == 'DIV':
                        val = eargs[0] // eargs[1]
                    elif op.name == 'EQ':
                        val = 1 if eargs[0] == eargs[1] else 0
                    #elif op.name == 'SHA3':
                    #    # μ′s[0]≡Keccak(μm[μs[0]...(μs[0] +μs[1]−1)])
                    #    raise Exception("re-eval_op: need support {}".format(op.name))
                    elif op.name in indirects:
                        depended_absts.add(op.pc)
                    elif op.name in externals:
                        depended_absts.add(op.pc)
                    else:
                        raise Exception("eval_op: need support {}".format(op.name))
                    if val != None: potential_consts.append(val)
                absts = flatten(absts)
                depended_absts.update(absts)

            visited.remove(op.pc)
            return potential_consts, depended_absts

    def findBlock(self, pc):
        for bb_pc in self.cfg.basic_blocks_from_addr:
            bb = self.cfg.basic_blocks_from_addr[bb_pc]
            if pc >= bb.start.pc and pc <= bb.end.pc:
                return bb

    def pre_eval(self):

        self.inst2block = {} # inst.pc : basicblock
        self.block2inst_mem = {} # basicblock : [inst.pc]
        self.block2inst_sto = {} # basicblock : [inst.pc]
        self.inst_cons_addr = {}
        self.inst_abst_addr = {}
        self.inst_cons_off = {}
        self.inst_abst_off = {}
        self.inst_cons_val = {}
        self.inst_abst_val = {}

        for mem_ops in [self.mwrites, self.mreads]:
            for pc in mem_ops:
                bb = self.findBlock(pc)
                self.inst2block[pc] = bb
                self.block2inst_mem.setdefault(bb, set()).add(pc)

        for sto_ops in [self.swrites, self.sreads]:
            for pc in sto_ops:
                bb = self.findBlock(pc)
                self.inst2block[pc] = bb
                self.block2inst_sto.setdefault(bb, set()).add(pc)

        for writes in [self.mwrites, self.swrites]:
            for pc in writes:
                for (addr, offset, val) in writes[pc]:
                    addr_cons, addr_abs = self.eval_op(addr, set(), 0)
                    off_cons, off_abs = self.eval_op(offset, set(), 0)
                    val_cons, val_abs = self.eval_op(val, set(), 0)
                    if addr_cons and off_cons and val_cons:
                        self.evaled.add(pc)
                    self.inst_cons_addr.setdefault(pc, set()).update(addr_cons)
                    self.inst_abst_addr.setdefault(pc, set()).update(addr_abs)
                    self.inst_cons_off.setdefault(pc, set()).update(off_cons)
                    self.inst_abst_off.setdefault(pc, set()).update(off_abs)
                    self.inst_cons_val.setdefault(pc, set()).update(val_cons)
                    self.inst_abst_val.setdefault(pc, set()).update(val_abs)

        for reads in [self.mreads, self.sreads]:
            for pc in reads:
                for (addr, offset) in reads[pc]:
                    addr_cons, addr_abs = self.eval_op(addr, set(), 0)
                    off_cons, off_abs = self.eval_op(offset, set(), 0)
                    # if addr_cons and off_cons: self.evaled.add(pc)
                    self.inst_cons_addr.setdefault(pc, set()).update(addr_cons)
                    self.inst_abst_addr.setdefault(pc, set()).update(addr_abs)
                    self.inst_cons_off.setdefault(pc, set()).update(off_cons)
                    self.inst_abst_off.setdefault(pc, set()).update(off_abs)

    def exist_re(self):
        print()
        print('evaled:', hl(self.evaled))
        print('connected:', hl(set(self.rw_dep.keys())))
        not_evaled = set(self.inst2block.keys()).difference(self.evaled)
        print('not evaled:', hl(not_evaled))
        for pc in not_evaled:
            self.show_data(pc)
        can = set()
        for pc in not_evaled:
            abst = self.inst_abst_addr[pc]
            abst_o = self.inst_abst_off[pc]
            abst_v = self.inst_abst_val.get(pc, set())
            if not abst.difference(self.evaled) \
                and not abst_o.difference(self.evaled) \
                and not abst_v.difference(self.evaled) \
                and self.cfg.instructions_from_addr[pc].name in indwrites:
                can.add(pc)
        print('can re-evaled writes:', can)
        print()
        return can


    def show_data(self, pc):
        print("""{}@{}
        addr
            - cons {}
            - abst {}
        offset
            - cons {}
            - abst {}
        value
            - cons {}
            - abst {}""".format(
                self.cfg.instructions_from_addr[pc].name,
                self.cfg.instructions_from_addr[pc].pc,
                self.inst_cons_addr.setdefault(pc, set()),
                self.inst_abst_addr.setdefault(pc, set()),
                self.inst_cons_off.setdefault(pc, set()),
                self.inst_abst_off.setdefault(pc, set()),
                self.inst_cons_val.setdefault(pc, set()),
                self.inst_abst_val.setdefault(pc, set())))


    def re_eval_write(self, pc):

        writes = self.mwrites if pc in self.mwrites else self.swrites

        for (addr, offset, val) in writes[pc]:
            addr_cons, addr_abs = self.re_eval_op(addr, set(), 0)
            off_cons, off_abs = self.re_eval_op(offset, set(), 0)
            val_cons, val_abs = self.re_eval_op(val, set(), 0)

            self.inst_cons_addr.setdefault(pc, set()).update(addr_cons)
            self.inst_abst_addr.setdefault(pc, set()).update(addr_abs)
            self.inst_cons_off.setdefault(pc, set()).update(off_cons)
            self.inst_abst_off.setdefault(pc, set()).update(off_abs)
            self.inst_cons_val.setdefault(pc, set()).update(val_cons)
            self.inst_abst_val.setdefault(pc, set()).update(val_abs)

            if addr_cons and off_cons and val_cons:
                self.evaled.add(pc)
            else:
                abst_a = self.inst_abst_addr[pc]
                abst_o = self.inst_abst_off[pc]
                abst_v = self.inst_abst_val.get(pc, set())
                if not abst_a.difference(self.evaled) \
                    and not abst_o.difference(self.evaled) \
                    and not abst_v.difference(self.evaled) \
                    and self.cfg.instructions_from_addr[pc].name in indwrites:
                    print("wrong here at ", pc, self.cfg.instructions_from_addr[pc].name)
                    self.inst_cons_addr.setdefault(pc, set())
                    self.show_data(pc)
                    print(self.evaled)
                    self.show_data(val.pc)
                    print(self.re_eval_op(val, set(), 0))
                    exit(0)

            if not val_cons and not val_abs:
                print("wrong empty"), exit(0)

    def re_eval_read(self, pc):

        reads = self.mreads if pc in self.mreads else self.sreads

        for (addr, offset) in reads[pc]:
            addr_cons, _ = self.re_eval_op(addr, set(), 0)
            off_cons, _ = self.re_eval_op(offset, set(), 0)
            self.inst_cons_addr.setdefault(pc, set()).update(addr_cons)
            self.inst_cons_off.setdefault(pc, set()).update(off_cons)

    def build_dependency(self):
        self.pre_eval()
        visited = set()

        loop = 0
        while True:
            if loop > 2000:
                print("fuck"), exit(0)
            loop += 1
            visited = self.build_addr_dependency(self.swrites, self.sreads, \
                                                self.block2inst_sto, visited)

            visited = self.build_addr_dependency(self.mwrites, self.mreads, \
                                                self.block2inst_mem, visited)

            re_pcs = self.exist_re()

            if not re_pcs: break

            for pc in re_pcs:
                self.re_eval_write(pc)

    def build_addr_dependency(self, writes, reads, b2i, visited):

        cons_writes = []

        while True:

            for pc in writes:
                if pc not in visited \
                        and self.inst_cons_addr[pc] \
                        and self.inst_cons_off[pc] \
                        and self.inst_cons_val[pc]:
                    cons_writes.append(pc)
                    visited.add(pc)

            if not cons_writes: break

            while cons_writes:
                pc = cons_writes.pop()
                self.cfg_depend_dfs(pc, self.inst2block[pc], b2i, reads, set(), 0)

            for pc in writes:
                if pc in visited: continue
                abst_a = self.inst_abst_addr[pc]
                abst_o = self.inst_abst_off[pc]
                abst_v = self.inst_abst_val.get(pc, set())
                if not abst_a.difference(self.evaled) and \
                        not abst_o.difference(self.evaled) and \
                        not abst_v.difference(self.evaled):
                    self.re_eval_write(pc)

        print('not visited writes', hl(set(writes.keys()).difference(visited)))
        return visited

    def cfg_depend_dfs(self, spc, curb, b2i, reads, visited, depth):

        print('depth:', depth, spc)
        cons_w = self.inst_cons_addr[spc]
        cons_wo = self.inst_cons_off[spc]

        if curb in visited: return []
        else: visited.add(curb)

        curins = b2i.get(curb, [])

        for pc in curins:

            if ((spc not in curins) or (spc in curins and pc > spc))\
                and self.cfg.instructions_from_addr[pc].name == \
                    self.cfg.instructions_from_addr[spc].name \
                and self.inst_cons_addr[pc].intersection(self.inst_cons_addr[spc]):
                visited.remove(curb)
                return [] # if re-write the same addr, not do the dfs
                          # still exists some prob here

            if pc in reads:
                cons_r = self.inst_cons_addr[pc]
                cons_ro = self.inst_cons_off[pc]
                if cons_r and cons_ro:
                    if overlap(cons_w, cons_wo, cons_r, cons_ro):
                    #if cons_r.intersection(cons_w): # old ver. not consider offset
                        self.rw_dep.setdefault(pc, set()).add(spc)
                        if self.cfg.instructions_from_addr[pc].name in ('SLOAD', 'MLOAD'):
                            self.evaled.add(pc)
                            print('propagate here w:', cons_w, cons_wo, self.inst_cons_val[spc], 'r:', cons_r, cons_ro)
                            self.inst_cons_val.setdefault(pc, set()).update(
                                    self.inst_cons_val[spc])
                        elif self.cfg.instructions_from_addr[pc].name == 'SHA3':
                            print('store inst pc:', spc)
                            print('check here w:', cons_w, cons_wo, self.inst_cons_val[spc], 'r:', cons_r, cons_ro)
                            #exit(0)
                        elif self.cfg.instructions_from_addr[pc].name in ('RETURN', 'CALL', 'CREATE', 'MSIZE'):
                            self.evaled.add(pc)
                        else:
                            print("please implement the operation of", self.cfg.instructions_from_addr[pc].name)
                            exit(0)

                else:
                    abst_r = self.inst_abst_addr[pc]
                    abst_ro = self.inst_abst_off[pc]
                    if not abst_r.difference(self.evaled) \
                        and not abst_ro.difference(self.evaled):
                        self.re_eval_read(pc)
                        cons_r = self.inst_cons_addr[pc]
                        cons_ro = self.inst_cons_off[pc]
                        if cons_r and cons_ro:
                            if overlap(cons_w, cons_wo, cons_r, cons_ro):
                            #if cons_r.intersection(cons_w):
                                # old ver. not consider offset
                                self.evaled.add(pc)
                                self.rw_dep.setdefault(pc, set()).add(spc)
                                self.inst_cons_val.setdefault(pc, set()).update(
                                        self.inst_cons_val[spc])

        #for abst_pc in
        for bb in curb.all_outgoing_basic_blocks:
            self.cfg_depend_dfs(spc, bb, b2i, reads, visited, depth + 1)

        visited.remove(curb)
