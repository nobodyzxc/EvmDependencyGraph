from z3 import *

solver = Solver()
current_state = None

class MachineState():
    #  machine state as tuple (g,pc,m,i,s)
    def __init__(self, gas, pc, mem, idx_mem_used, stk):
        self.pc  = pc
        self.gas = gas
        self.mem = mem.copy()
        self.stk = stk.copy()
        self.idx_mem = idx_mem_used
        self.path_condition = []

def sym_exec_scc_graph(scc_graph):
    loop = 0
    queue = [scc_graph.root]
    while len(queue) != 0:
        if all_entries_exist_state(queue[0]):
            loop = 0
            sym_exec_scc(queue[0])
        elif loop > len(queue):
            print('unsolvable status'), exit(1)
        else:
            loop += 1
            queue.append(queue.pop(0))

def sym_exec_scc(scc):
    global current_state
    for entry in scc.states:
        # may exist many states but apply states[0] first
        current_state = scc.states[0].copy()
        sym_exec_block(scc, entry, current_state)

def sym_exec_block(scc, block, state):
    pass

def sym_exec_ins():
    pass
