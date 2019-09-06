import sys
from .dg import DG
from .cfg.function import Function
from .stack import AbstStack, ListStack


BASIC_BLOCK_END = ['STOP',
                   'SELFDESTRUCT',
                   'RETURN',
                   'REVERT',
                   'INVALID',
                   'SUICIDE',
                   'JUMP',
                   'JUMPI']

class StackValueAnalysis(object):
    '''
        Stack value analysis.
        After each convergence, we add the new branches, update the binja view
        and re-analyze the function. The exploration is bounded in case the
        analysis is lost.
    '''

    def __init__(self,
                 cfg,
                 dg,
                 entry_point,
                 key,
                 maxiteration=1000,
                 maxexploration=100,
                 initStack=None):
        '''
        Args:
            maxiteration (int): number of time re-analyze the function
            maxexploration (int): number of time re-explore a bb
        '''
        # last targets discovered. We keep track of these branches to only
        # re-launch the analysis on new paths found
        self.last_discovered_targets = {}

        # all the targets discovered
        self.all_discovered_targets = {}
        self.stacksIn = {}
        self.stacksOut = {}

        # bb counter, to bound the bb exploration
        self.bb_counter = {}

        # number of time the function was analysis, to bound the analysis
        # recursion
        self.counter = 0

        # limit the number of time we re-analyze a function
        self.MAXITERATION = maxiteration

        # limit the number of time we explore a basic block (unrool)
        self.MAXEXPLORATION = maxexploration

        self.initStack = initStack

        self._entry_point = entry_point

        self.cfg = cfg

        self.dg = dg

        self._key = key

        self._basic_blocks_explored = []

        self._to_explore = {self._entry_point}

        self._outgoing_basic_blocks = []

    def is_jumpdst(self, addr):
        '''
            Check that an instruction is a JUMPDEST
            A JUMP to no-JUMPDEST instruction is not valid (see yellow paper).
            Yet some assembly tricks use a JUMP to an invalid instruction to
            trigger THROW. We need to filter those jumps
        Args:
            addr (int)
        Returns:
            bool: True if the instruction is a JUMPDEST
        '''
        if not addr in self.cfg.instructions_from_addr:
            return False
        ins = self.cfg.instructions_from_addr[addr]
        return ins.name == 'JUMPDEST'

    #def stub(self, ins, addr, stack):
    #    return (False, None)

    def _transfer_func_ins(self, ins, addr, stacks):
        ostk, istk = stacks
        oprdStack = AbstStack().copy_stack(ostk)
        instStack = ListStack().copy_stack(istk)

        # useless?
        #(is_stub, stub_ret) = self.stub(ins, addr, stack)
        #if is_stub:
        #    return stub_ret

        op = ins.name
        if op.startswith('PUSH'):
            instStack.push(ins)
            oprdStack.push(ins.operand)
        elif op.startswith('SWAP'):
            nth_elem = int(op[4:])
            instStack.swap(nth_elem)
            oprdStack.swap(nth_elem)
        elif op.startswith('DUP'):
            nth_elem = int(op[3:])
            instStack.dup(nth_elem)
            oprdStack.dup(nth_elem)
        elif op == 'AND':
            v1 = oprdStack.pop()
            v2 = oprdStack.pop()
            oprdStack.push(v1.absAnd(v2))

            for s in instStack._insts:
                v1 = s.pop() if s else None
                v2 = s.pop() if s else None
                s.append(ins)
                self.dg.add_edges(ins, [v1, v2])

        # For all the other opcode: remove
        # the pop elements, and push None elements
        # if JUMP or JUMPI saves the last value before poping
        else:
            n_pop = ins.pops
            n_push = ins.pushes
            for _ in range(0, n_pop):
                oprdStack.pop()

            args = []

            for s in instStack._insts:
                args = [s.pop() if s else None for _ in range(0, n_pop)]
                self.dg.add_edges(ins, args)
                self.dg.record_ins(ins, args)

            for _ in range(0, n_push):
                oprdStack.push(None)
                instStack.push(ins)


        return oprdStack, instStack

    def _explore_bb(self, bb, stacks):
        '''
            Update the stack of a basic block. Return the last jump/jumpi
            target

            The last jump value is returned, as the JUMP/JUMPI instruction will
            pop the value before returning the function

            self.stacksOut will contain the stack of last instruction of the
            basic block.
        Args:
            bb
            stack (Stack)
        Returns:
            AbsStackElem: last jump computed.
        '''
        last_jump = None

        if not bb.start.pc in self._basic_blocks_explored:
            self._basic_blocks_explored.append(bb.start.pc)

        ins = None
        for ins in bb.instructions:
            addr = ins.pc
            self.stacksIn[addr] = stacks
            stacks = self._transfer_func_ins(ins, addr, stacks)

            self.stacksOut[addr] = stacks

        if ins:
            # if we are going to do a jump / jumpi
            # get the destination
            op = ins.name
            if op == 'JUMP' or op == 'JUMPI':
                oprdStack, _ = stacks
                last_jump = oprdStack.top()
        return last_jump

    def _transfer_func_bb(self, bb, init=False):
        '''
            Transfer function
        '''

        if self._key == Function.DISPATCHER_ID and bb.reacheable:
            return
        addr = bb.start.pc
        end_ins = bb.end
        end = end_ins.pc

        # bound the number of times we analyze a BB
        if addr not in self.bb_counter:
            self.bb_counter[addr] = 1
        else:
            self.bb_counter[addr] += 1

            if self.bb_counter[addr] > self.MAXEXPLORATION:
                # print('Reach max explo {}'.format(hex(addr)))
                return

        # Check if the bb was already analyzed (used for convergence)
        if end in self.stacksOut:
            prev_stacks = self.stacksOut[end]
        else:
            prev_stacks = None


        if init and self.initStack:
            oprdStack = self.initStack
        else:
            oprdStack = AbstStack()

        instStack = ListStack()

        # Merge all the stack incoming_basic_blocks
        # We merge only father that were already analyzed
        incoming_basic_blocks = bb.incoming_basic_blocks(self._key)

        incoming_basic_blocks = [f for f in incoming_basic_blocks if f.end.pc in self.stacksOut]

        if incoming_basic_blocks:
            father = incoming_basic_blocks[0]
            incoming_basic_blocks = incoming_basic_blocks[1::]
            out_ostk, out_istk = self.stacksOut[father.end.pc]
            oprdStack.copy_stack(out_ostk)
            instStack.copy_stack(out_istk)
            for father in incoming_basic_blocks:
                oprdStack = oprdStack.merge(out_ostk)
                instStack = instStack.merge(out_istk)
        # Analyze the BB
        self._explore_bb(bb, (oprdStack, instStack))

        # check if the last instruction is a JUMP
        op = end_ins.name

        if op == 'JUMP':
            src = end

            dst = self.stacksIn[end][0].top().get_vals()

            if dst:
                dst = [x for x in dst if x and self.is_jumpdst(x)]

                self.add_branches(src, dst)

        elif op == 'JUMPI':
            src = end

            dst = self.stacksIn[end][0].top().get_vals()
            if dst:
                dst = [x for x in dst if x and self.is_jumpdst(x)]

                self.add_branches(src, dst)

        # check for convergence
        converged = False

        if prev_stacks:
            if prev_stacks[0].equals(self.stacksOut[end][0]):
                converged = True

        if not converged:
            new_outgoing_basic_blocks = bb.outgoing_basic_blocks(self._key)
            self._outgoing_basic_blocks = new_outgoing_basic_blocks + self._outgoing_basic_blocks

    def add_branches(self, src, dst):
        '''
            Add new branches
        Ags:
            src (int)
            dst (list of int)
        '''
        if src not in self.all_discovered_targets:
            self.all_discovered_targets[src] = set()

        for d in dst:
            if d not in self.all_discovered_targets[src]:
                if src not in self.last_discovered_targets:
                    self.last_discovered_targets[src] = set()

                self.last_discovered_targets[src].add(d)

                self.all_discovered_targets[src].add(d)

    def explore(self):
        """
            Launch the analysis
        """
        init = False

        bb = self._to_explore.pop()

        self._transfer_func_bb(bb, init)
        while self._outgoing_basic_blocks:
            self._transfer_func_bb(self._outgoing_basic_blocks.pop())

        last_discovered_targets = self.last_discovered_targets
        self.last_discovered_targets = {}

        for src, dsts in last_discovered_targets.items():
            bb_from = self.cfg.basic_blocks_from_addr[src]
            for dst in dsts:
                bb_to = self.cfg.basic_blocks_from_addr[dst]

                bb_from.add_outgoing_basic_block(bb_to, self._key)
                bb_to.add_incoming_basic_block(bb_from, self._key)

        dsts = [dests for (src, dests) in last_discovered_targets.items()]
        self._to_explore |= {self.cfg.basic_blocks_from_addr[item] for sublist in dsts for item in sublist}

    def analyze(self):
        self.cfg.compute_simple_edges(self._key)
        while self._to_explore:
            self.explore()

        self.cfg.compute_reachability(self._entry_point, self._key)

        return self._basic_blocks_explored
