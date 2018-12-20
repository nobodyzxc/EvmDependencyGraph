from z3 import *
# from scc import MachineState

solver = Solver()
visited_edge = set()
current_state = None

def init_current_state(state):
    global solver
    global visited_edge
    global current_state
    visited_edge.clear()
    current_state = state.copy()
    solver.reset()
    for constraints in state.constraints:
        solver.append(constraints)

def all_entries_exist_state(scc):
    return all([e != None for e in scc.states.values()])

def sym_exec_scc_graph(scc_graph):
    loop = 0
    queue = [scc_graph.root]
    visited_sccs = set()
    while len(queue) != 0:
        if all_entries_exist_state(queue[0]):
            loop = 0
            sym_exec_scc(scc_graph, queue[0])
            visited_sccs.add(queue[0])
            queue.extend(
                    queue[0].outgoing_sccs() \
                            .difference(visited_sccs))
            queue.pop(0)
        elif loop > len(queue):
            print('unsolvable status'), exit(1)
        else:
            loop += 1
            queue.append(queue.pop(0))

def sym_exec_scc(scc_graph, scc):
    for entry in scc.states:
        # may exist many states but apply states[0] first
        init_current_state(scc.states[entry][0])
        # ^ retain the state
        # and copy a new one to current for execution
        sym_exec_block(scc_graph, scc, entry, current_state)

def sym_exec_block(scc_graph, scc, block, state):
    global visited_edge
    global branch_expr
    global jump_dest
    global solver
    jump_dest = []

    for instr in block.instructions:
        sym_exec_ins(instr)

    if block.end.name == 'JUMP':
        dest = jump_dest
        if (block, dest) in visited_edge:
            return # duplicated path
        elif dest not in scc.vertices:
            # next scc, store state, stop execution
            scc_graph.scc_set[dest].states[dest].append(state)
        else:
            visited_edge.add((block, dest))
            sym_exec_block(scc_graph, scc, dest, state)
    elif block.end.name == 'JUMPI':
        true_dest, false_dest = jump_dest, scc_graph.find_falls_to(block)
        true_branch_expr, false_branch_expr = branch_expr, Not(branch_expr)

        solver.push()
        solver.add(true_branch_expr)

        try:
            if solver.check() == unsat:
                print("infeasible path on", true_branch_expr)
            else:
                sym_exec_block(scc_graph, scc, true_dest, state.copy(true_branch_expr))
        except Exception as e:
            print("true branch Exception:", e)

        solver.pop()
        solver.push()
        solver.add(false_branch_expr)

        try:
            if solver.check() == unsat:
                print("infeasible path on", branch_expr)
            else:
                sym_exec_block(scc_graph, scc, false_dest, state.copy(false_branch_expr))
        except Exception as e:
            print("false branch Exception:", e)

        solver.pop()

    else:
        # falls_to? terminal?
        return # end of the dfs

def sym_exec_ins(instr):
    global branch_expr
    global jump_dest
    print(instr)
