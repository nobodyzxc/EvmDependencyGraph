from z3 import *
from vargenerator import *
from calculate import *
from util import *
import zlib, base64
# from scc import MachineState

solver = Solver()
gen = Generator()
#visited_edge = set()
visited_edge = {}
current_state = None

MSIZE = False

UNSIGNED_BOUND_NUMBER = 2**256 - 1
CONSTANT_ONES_159 = BitVecVal((1 << 160) - 1, 256)

terminal_opcode = ("STOP" ,"RETURN" ,"SUICIDE" ,
        "REVERT" ,"ASSERTFAIL", "INVALID")

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
    return all([e for e in scc.states.values()])

def sym_exec_scc_graph(scc_graph, bytecode):
    global evm_code
    global MSIZE

    evm_code = bytecode
    MSIZE = True if 'MSIZE' in [ins.name for ins in scc_graph.cfg.instructions] else False
    print('block number:', len(scc_graph.unvisited_blocks))
    print('scc   number:', len(scc_graph.unvisited_sccs))

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
            print('unsolvable status')
            print(queue[0].vertices)
            print(scc_graph.unvisited_blocks)
            print(scc_graph.unvisited_sccs)
            print('block number:', len(scc_graph.unvisited_blocks))
            print('scc   number:', len(scc_graph.unvisited_sccs))
            return
            # exit(1)
        else:
            loop += 1
            queue.append(queue.pop(0))

def sym_exec_scc(scc_graph, scc):

    scc_graph.unvisited_sccs.remove(scc)

    for entry in scc.states:
        # may exist many states but apply states[0] first
        init_current_state(scc.states[entry][0])
        # ^ retain the state
        # and copy a new one to current for execution
        sym_exec_block(scc_graph, scc, entry, current_state)

def on_scc_border_or_loop_limit(
        scc_graph, scc, block, dest, state):
    global visited_edge
    if visited_edge.get((block, dest), 0) > 20:
        return True # duplicated path
    elif dest not in scc.vertices:
        # next scc, store state, stop execution
        state.pc = dest.start.pc
        scc_graph.scc_set[dest].states[dest].append(state)
        return True
    else:
        return False

def sym_exec_block(scc_graph, scc, block, state):
    global visited_edge
    global branch_expr
    global solver

    scc_graph.unvisited_blocks.remove(block)

    for instr in block.instructions:
        dest = sym_exec_ins(instr, state)

    if dest: dest = scc_graph.cfg.basic_blocks_from_addr[dest]

    if block.end.name == 'JUMP':
        # unconditoinal
        if not on_scc_border_or_loop_limit(
                scc_graph, scc, block, dest, state):
            visited_edge[(block, dest)] = \
                    visited_edge.get((block, dest), 0) + 1
            sym_exec_block(scc_graph, scc, dest, state)
            visited_edge[(block, dest)] -= 1

    elif block.end.name == 'JUMPI':
        # conditional
        true_dest, false_dest = dest, scc_graph.get_falls_to(block)
        true_branch_expr, false_branch_expr = branch_expr, Not(branch_expr)

        solver.push()
        solver.add(true_branch_expr)

        try:
            if solver.check() == unsat:
                print("infeasible path on", true_branch_expr)
            elif not on_scc_border_or_loop_limit(
                    scc_graph, scc, block, true_dest, state):
                visited_edge[(block, true_dest)] = \
                        visited_edge.get(
                                (block, true_dest), 0) + 1
                sym_exec_block(scc_graph, scc,
                        true_dest, state.copy(true_branch_expr))
                visited_edge[(block, true_dest)] -= 1

        except Exception as e:
            print("true branch Exception:", e)

        solver.pop()
        solver.push()
        solver.add(false_branch_expr)

        try:
            if solver.check() == unsat:
                print("infeasible path on", false_branch_expr)
            elif not on_scc_border_or_loop_limit(
                    scc_graph, scc, block, false_dest, state):
                visited_edge[(block, false_dest)] = \
                        visited_edge.get(
                                (block, false_dest), 0) + 1
                sym_exec_block(scc_graph, scc,
                        false_dest, state.copy(false_branch_expr))
                visited_edge[(block, false_dest)] -= 1
        except Exception as e:
            print("false branch Exception:", e)

        solver.pop()

    elif block.end.name in terminal_opcode :
        scc_graph.states.setdefault(block, []).append(state)
    else:
        dest = scc_graph.get_falls_to(block)
        if not on_scc_border_or_loop_limit(
                scc_graph, scc, block, dest, state):
            visited_edge[(block, dest)] = \
                    visited_edge.get((block, dest), 0) + 1
            visited_edge.add((block, dest))
            sym_exec_block(scc_graph, scc, dest, state)
            visited_edge[(block, dest)] -= 1

def sym_exec_ins(instr, state):
    global gen
    global solver
    global branch_expr

    global evm_code

    mem = state.mem
    stack = state.stack
    memory = state.memory
    variables = state.variables
    sha3_list = state.sha3_list

    opcode = instr.name

    if opcode in ("INVALID", "ASSERTFAIL"): return

    gas_increment, gas_constraints = \
            calculate_gas(opcode, state, solver)

    state.gas += gas_increment
    state.gas_constraints.append(gas_constraints)

    #
    #  0s: Stop and Arithmetic Operations
    #
    if opcode == "STOP":
        state.pc += 1
        return
    elif opcode == "ADD":
        if len(stack) > 1:
            state.pc += 1
            first = stack.pop(0)
            second = stack.pop(0)
            # Type conversion is needed
            # when they are mismatched
            if isReal(first) and isSymbolic(second):
                first = BitVecVal(first, 256)
                computed = first + second
            elif isSymbolic(first) and isReal(second):
                second = BitVecVal(second, 256)
                computed = first + second
            else:
                # both are real and we need to manually modulus with 2 ** 256
                # if both are symbolic z3 takes care of modulus automatically
                computed = (first + second) % (2 ** 256)
            computed = simplify(computed) if is_expr(computed) else computed

            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MUL":
        if len(stack) > 1:
            state.pc += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isReal(first) and isSymbolic(second):
                first = BitVecVal(first, 256)
            elif isSymbolic(first) and isReal(second):
                second = BitVecVal(second, 256)
            computed = first * second & UNSIGNED_BOUND_NUMBER
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SUB":
        if len(stack) > 1:
            state.pc += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isReal(first) and isSymbolic(second):
                first = BitVecVal(first, 256)
                computed = first - second
            elif isSymbolic(first) and isReal(second):
                second = BitVecVal(second, 256)
                computed = first - second
            else:
                computed = (first - second) % (2 ** 256)
            computed = simplify(computed) if is_expr(computed) else computed

            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "DIV":
        if len(stack) > 1:
            state.pc += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if second == 0:
                    computed = 0
                else:
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    computed = first / second
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add( Not (second == 0) )
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    computed = UDiv(first, second)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SDIV":
        if len(stack) > 1:
            state.pc += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_signed(first)
                second = to_signed(second)
                if second == 0:
                    computed = 0
                elif first == -2**255 and second == -1:
                    computed = -2**255
                else:
                    sign = -1 if (first / second) < 0 else 1
                    computed = sign * ( abs(first) / abs(second) )
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add(Not(second == 0))
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    solver.push()
                    solver.add( Not( And(first == -2**255, second == -1 ) ))
                    if check_sat(solver) == unsat:
                        computed = -2**255
                    else:
                        solver.push()
                        solver.add(first / second < 0)
                        sign = -1 if check_sat(solver) == sat else 1
                        z3_abs = lambda x: If(x >= 0, x, -x)
                        first = z3_abs(first)
                        second = z3_abs(second)
                        computed = sign * (first / second)
                        solver.pop()
                    solver.pop()
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MOD":
        if len(stack) > 1:
            state.pc += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if second == 0:
                    computed = 0
                else:
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    computed = first % second & UNSIGNED_BOUND_NUMBER
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)

                solver.push()
                solver.add(Not(second == 0))
                if check_sat(solver) == unsat:
                    # it is provable that second is indeed equal to zero
                    computed = 0
                else:
                    computed = URem(first, second)
                solver.pop()

            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SMOD":
        if len(stack) > 1:
            state.pc += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if second == 0:
                    computed = 0
                else:
                    first = to_signed(first)
                    second = to_signed(second)
                    sign = -1 if first < 0 else 1
                    computed = sign * (abs(first) % abs(second))
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)

                solver.push()
                solver.add(Not(second == 0))
                if check_sat(solver) == unsat:
                    # it is provable that second is indeed equal to zero
                    computed = 0
                else:

                    solver.push()
                    solver.add(first < 0) # check sign of first element
                    sign = BitVecVal(-1, 256) if check_sat(solver) == sat \
                        else BitVecVal(1, 256)
                    solver.pop()

                    z3_abs = lambda x: If(x >= 0, x, -x)
                    first = z3_abs(first)
                    second = z3_abs(second)

                    computed = sign * (first % second)
                solver.pop()

            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "ADDMOD":
        if len(stack) > 2:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            third = stack.pop(0)

            if isAllReal(first, second, third):
                if third == 0:
                    computed = 0
                else:
                    computed = (first + second) % third
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add( Not(third == 0) )
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    first = ZeroExt(256, first)
                    second = ZeroExt(256, second)
                    third = ZeroExt(256, third)
                    computed = (first + second) % third
                    computed = Extract(255, 0, computed)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MULMOD":
        if len(stack) > 2:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            third = stack.pop(0)

            if isAllReal(first, second, third):
                if third == 0:
                    computed = 0
                else:
                    computed = (first * second) % third
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add( Not(third == 0) )
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    first = ZeroExt(256, first)
                    second = ZeroExt(256, second)
                    third = ZeroExt(256, third)
                    computed = URem(first * second, third)
                    computed = Extract(255, 0, computed)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "EXP":
        if len(stack) > 1:
            state.pc += 1
            base = stack.pop(0)
            exponent = stack.pop(0)
            # Type conversion is needed when they are mismatched
            if isAllReal(base, exponent):
                computed = pow(base, exponent, 2**256)
            else:
                # The computed value is unknown, this is because power is
                # not supported in bit-vector theory
                new_var_name = gen.gen_arbitrary_var()
                computed = BitVec(new_var_name, 256)
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SIGNEXTEND":
        if len(stack) > 1:
            state.pc += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if first >= 32 or first < 0:
                    computed = second
                else:
                    signbit_index_from_right = 8 * first + 7
                    if second & (1 << signbit_index_from_right):
                        computed = second | (2 ** 256 - (1 << signbit_index_from_right))
                    else:
                        computed = second & ((1 << signbit_index_from_right) - 1 )
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add( Not( Or(first >= 32, first < 0 ) ) )
                if check_sat(solver) == unsat:
                    computed = second
                else:
                    signbit_index_from_right = 8 * first + 7
                    solver.push()
                    solver.add(second & (1 << signbit_index_from_right) == 0)
                    if check_sat(solver) == unsat:
                        computed = second | (2 ** 256 - (1 << signbit_index_from_right))
                    else:
                        computed = second & ((1 << signbit_index_from_right) - 1)
                    solver.pop()
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    #
    #  10s: Comparison and Bitwise Logic Operations
    #
    elif opcode == "LT":
        if len(stack) > 1:
            state.pc += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_unsigned(first)
                second = to_unsigned(second)
                if first < second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(ULT(first, second), BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "GT":
        if len(stack) > 1:
            state.pc += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_unsigned(first)
                second = to_unsigned(second)
                if first > second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(UGT(first, second), BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SLT":  # Not fully faithful to signed comparison
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_signed(first)
                second = to_signed(second)
                if first < second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(first < second, BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SGT":  # Not fully faithful to signed comparison
        if len(stack) > 1:
            state.pc += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_signed(first)
                second = to_signed(second)
                computed = 1 if first > second else 0
            else:
                computed = If(first > second, BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "EQ":
        if len(stack) > 1:
            state.pc += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                computed = 1 if first == second else 0
            else:
                computed = If(first == second, BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "ISZERO":
        # Tricky: this instruction works on both boolean and integer,
        # when we have a symbolic expression, type error might occur
        # Currently handled by try and catch
        if len(stack) > 0:
            state.pc += 1
            first = stack.pop(0)
            if isReal(first):
                computed = 1 if first == 0 else 0
            else:
                computed = If(first == 0, BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "AND":
        if len(stack) > 1:
            state.pc += 1
            first = stack.pop(0)
            second = stack.pop(0)
            computed = first & second
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "OR":
        if len(stack) > 1:
            state.pc += 1
            first = stack.pop(0)
            second = stack.pop(0)

            computed = first | second
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)

        else:
            raise ValueError('STACK underflow')
    elif opcode == "XOR":
        if len(stack) > 1:
            state.pc += 1
            first = stack.pop(0)
            second = stack.pop(0)

            computed = first ^ second
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)

        else:
            raise ValueError('STACK underflow')
    elif opcode == "NOT":
        if len(stack) > 0:
            state.pc += 1
            first = stack.pop(0)
            computed = (~first) & UNSIGNED_BOUND_NUMBER
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "BYTE":
        if len(stack) > 1:
            state.pc += 1
            first = stack.pop(0)
            byte_index = 32 - first - 1
            second = stack.pop(0)

            if isAllReal(first, second):
                if first >= 32 or first < 0:
                    computed = 0
                else:
                    computed = second & (255 << (8 * byte_index))
                    computed = computed >> (8 * byte_index)
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add( Not (Or( first >= 32, first < 0 ) ) )
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    computed = second & (255 << (8 * byte_index))
                    computed = computed >> (8 * byte_index)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    #
    # 20s: SHA3
    #
    elif opcode == "SHA3":
        if len(stack) > 1:
            state.pc += 1
            s0 = stack.pop(0)
            s1 = stack.pop(0)
            if isAllReal(s0, s1):
                # simulate the hashing of sha3
                data = [str(x) for x in memory[s0: s0 + s1]]
                position = ''.join(data)
                position = re.sub('[\s+]', '', position)
                position = zlib.compress(six.b(position), 9)
                position = base64.b64encode(position)
                position = position.decode('utf-8', 'strict')
                if position in sha3_list:
                    stack.insert(0, sha3_list[position])
                else:
                    new_var_name = gen.gen_arbitrary_var()
                    new_var = BitVec(new_var_name, 256)
                    sha3_list[position] = new_var
                    stack.insert(0, new_var)
            else:
                # push into the execution a fresh symbolic variable
                new_var_name = gen.gen_arbitrary_var()
                new_var = BitVec(new_var_name, 256)
                variables[new_var_name] = new_var
                stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    #
    # 30s: Environment Information
    #
    elif opcode == "ADDRESS":  # get address of currently executing account
        state.pc += 1
        stack.insert(0, variables["Ia"])
    elif opcode == "BALANCE":
        if len(stack) > 0:
            state.pc += 1
            address = stack.pop(0)
            # if isReal(address) and global_params.USE_GLOBAL_BLOCKCHAIN:
            #     new_var = data_source.getBalance(address)
            # else:
            new_var_name = gen.gen_balance_var()
            if new_var_name in variables:
                new_var = variables[new_var_name]
            else:
                new_var = BitVec(new_var_name, 256)
                variables[new_var_name] = new_var
            if isReal(address):
                hashed_address = "concrete_address_" + str(address)
            else:
                hashed_address = str(address)
            state.balance[hashed_address] = new_var
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CALLER":  # get caller address
        # that is directly responsible for this execution
        state.pc += 1
        stack.insert(0, state.sender_address)
    elif opcode == "ORIGIN":  # get execution origination address
        state.pc += 1
        stack.insert(0, state.origin)
    elif opcode == "CALLVALUE":  # get value of this transaction
        state.pc += 1
        stack.insert(0, state.deposited_value)
    elif opcode == "CALLDATALOAD":  # from input data from environment
        if len(stack) > 0:
            state.pc += 1
            position = stack.pop(0)
            # if g_src_map:
            #     source_code = g_src_map.get_source_code(global_state['pc'] - 1)
            #     if source_code.startswith("function") and isReal(position) and current_func_name in g_src_map.func_name_to_params:
            #         params =  g_src_map.func_name_to_params[current_func_name]
            #         param_idx = (position - 4) // 32
            #         for param in params:
            #             if param_idx == param['position']:
            #                 new_var_name = param['name']
            #                 g_src_map.var_names.append(new_var_name)
            #     else:
            #         new_var_name = gen.gen_data_var(position)
            # else:
            new_var_name = gen.gen_data_var(position)
            if new_var_name in variables:
                new_var = variables[new_var_name]
            else:
                new_var = BitVec(new_var_name, 256)
                variables[new_var_name] = new_var
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CALLDATASIZE":
        state.pc += 1
        new_var_name = gen.gen_data_size()
        if new_var_name in variables:
            new_var = variables[new_var_name]
        else:
            new_var = BitVec(new_var_name, 256)
            variables[new_var_name] = new_var
        stack.insert(0, new_var)
    elif opcode == "CALLDATACOPY":
        # Copy input data to memory
        # TODO: Don't know how to simulate this yet
        if len(stack) > 2:
            state.pc += 1
            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CODESIZE":
        stack.insert(0, len(evm_code) / 2)
    elif opcode == "CODECOPY":
        if len(stack) > 2:
            state.pc += 1
            mem_location = stack.pop(0)
            code_from = stack.pop(0)
            no_bytes = stack.pop(0)
            current_miu_i = state.miu_i

            if isAllReal(mem_location, current_miu_i, code_from, no_bytes):
                if six.PY2:
                    temp = long(math.ceil((mem_location + no_bytes) / float(32)))
                else:
                    temp = int(math.ceil((mem_location + no_bytes) / float(32)))

                if temp > current_miu_i:
                    current_miu_i = temp

                evm = evm_file.read()[:-1]
                start = code_from * 2
                end = start + no_bytes * 2
                code = evm_code[start: end]

                mem[mem_location] = int(code, 16)
            else:
                new_var_name = gen.gen_code_var("Ia", code_from, no_bytes)
                if new_var_name in variables:
                    new_var = variables[new_var_name]
                else:
                    new_var = BitVec(new_var_name, 256)
                    variables[new_var_name] = new_var

                temp = ((mem_location + no_bytes) / 32) + 1
                current_miu_i = to_symbolic(current_miu_i)
                expression = current_miu_i < temp
                solver.push()
                solver.add(expression)
                if MSIZE:
                    if check_sat(solver) != unsat:
                        current_miu_i = If(expression, temp, current_miu_i)
                solver.pop()
                mem.clear() # very conservative
                mem[str(mem_location)] = new_var
            state.miu_i = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif opcode == "RETURNDATACOPY":
        if len(stack) > 2:
            state.pc += 1
            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "RETURNDATASIZE":
        state.pc += 1
        new_var_name = gen.gen_arbitrary_var()
        new_var = BitVec(new_var_name, 256)
        stack.insert(0, new_var)
    elif opcode == "GASPRICE":
        state.pc += 1
        stack.insert(0, state.gas_price)
    elif opcode == "EXTCODESIZE":
        if len(stack) > 0:
            state.pc += 1
            address = stack.pop(0)
            # if isReal(address) and global_params.USE_GLOBAL_BLOCKCHAIN:
            #     code = data_source.getCode(address)
            #     stack.insert(0, len(code)/2)
            # else:
            # not handled yet
            new_var_name = gen.gen_code_size_var(address)
            if new_var_name in variables:
                new_var = variables[new_var_name]
            else:
                new_var = BitVec(new_var_name, 256)
                variables[new_var_name] = new_var
                stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "EXTCODECOPY":
        if len(stack) > 3:
            state.pc += 1
            address = stack.pop(0)
            mem_location = stack.pop(0)
            code_from = stack.pop(0)
            no_bytes = stack.pop(0)
            current_miu_i = state.miu_i

            # if isAllReal(address, mem_location, current_miu_i, code_from, no_bytes) and USE_GLOBAL_BLOCKCHAIN:
            #     if six.PY2:
            #         temp = long(math.ceil((mem_location + no_bytes) / float(32)))
            #     else:
            #         temp = int(math.ceil((mem_location + no_bytes) / float(32)))
            #     if temp > current_miu_i:
            #         current_miu_i = temp

            #     evm = data_source.getCode(address)
            #     start = code_from * 2
            #     end = start + no_bytes * 2
            #     code = evm[start: end]
            #     mem[mem_location] = int(code, 16)
            # else:
            new_var_name = gen.gen_code_var(address, code_from, no_bytes)
            if new_var_name in variables:
                new_var = variables[new_var_name]
            else:
                new_var = BitVec(new_var_name, 256)
                variables[new_var_name] = new_var

            temp = ((mem_location + no_bytes) / 32) + 1
            current_miu_i = to_symbolic(current_miu_i)
            expression = current_miu_i < temp
            solver.push()
            solver.add(expression)
            if MSIZE:
                if check_sat(solver) != unsat:
                    current_miu_i = If(expression, temp, current_miu_i)
            solver.pop()
            mem.clear() # very conservative
            mem[str(mem_location)] = new_var

            state.miu_i = current_miu_i
        else:
            raise ValueError('STACK underflow')
    #
    #  40s: Block Information
    #
    elif opcode == "BLOCKHASH":  # information from block header
        if len(stack) > 0:
            state.pc += 1
            stack.pop(0)
            new_var_name = "IH_blockhash"
            if new_var_name in variables:
                new_var = variables[new_var_name]
            else:
                new_var = BitVec(new_var_name, 256)
                variables[new_var_name] = new_var
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "COINBASE":
        # information from block header
        state.pc += 1
        stack.insert(0, state.currentCoinbase)
    elif opcode == "TIMESTAMP":
        # information from block header
        state.pc += 1
        stack.insert(0, state.currentTimestamp)
    elif opcode == "NUMBER":
        # information from block header
        state.pc += 1
        stack.insert(0, state.currentNumber)
    elif opcode == "DIFFICULTY":
        # information from block header
        state.pc += 1
        stack.insert(0, state.currentDifficulty)
    elif opcode == "GASLIMIT":
        # information from block header
        state.pc += 1
        stack.insert(0, state.currentGasLimit)
    #
    #  50s: Stack, Memory, Storage, and Flow Information
    #
    elif opcode == "POP":
        if len(stack) > 0:
            state.pc += 1
            stack.pop(0)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MLOAD":
        if len(stack) > 0:
            state.pc += 1
            address = stack.pop(0)
            current_miu_i = state.miu_i
            if isAllReal(address, current_miu_i) and address in mem:
                if six.PY2:
                    temp = long(math.ceil((address + 32) / float(32)))
                else:
                    temp = int(math.ceil((address + 32) / float(32)))
                if temp > current_miu_i:
                    current_miu_i = temp
                value = mem[address]
                stack.insert(0, value)
            else:
                temp = ((address + 31) / 32) + 1
                current_miu_i = to_symbolic(current_miu_i)
                expression = current_miu_i < temp
                solver.push()
                solver.add(expression)
                if MSIZE:
                    if check_sat(solver) != unsat:
                        # this means that it is possibly that current_miu_i < temp
                        current_miu_i = If(expression,temp,current_miu_i)
                solver.pop()
                new_var_name = gen.gen_mem_var(address)
                if new_var_name in variables:
                    new_var = variables[new_var_name]
                else:
                    new_var = BitVec(new_var_name, 256)
                    variables[new_var_name] = new_var
                stack.insert(0, new_var)
                if isReal(address):
                    mem[address] = new_var
                else:
                    mem[str(address)] = new_var
            state.miu_i = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MSTORE":
        if len(stack) > 1:
            state.pc += 1
            stored_address = stack.pop(0)
            stored_value = stack.pop(0)
            current_miu_i = state.miu_i
            if isReal(stored_address):
                # preparing data for hashing later
                old_size = len(memory) // 32
                new_size = ceil32(stored_address + 32) // 32
                mem_extend = (new_size - old_size) * 32
                memory.extend([0] * mem_extend)
                value = stored_value
                for i in range(31, -1, -1):
                    memory[stored_address + i] = value % 256
                    value /= 256
            if isAllReal(stored_address, current_miu_i):
                if six.PY2:
                    temp = long(math.ceil((stored_address + 32) / float(32)))
                else:
                    temp = int(math.ceil((stored_address + 32) / float(32)))
                if temp > current_miu_i:
                    current_miu_i = temp
                mem[stored_address] = stored_value  # note that the stored_value could be symbolic
            else:
                temp = ((stored_address + 31) / 32) + 1
                expression = current_miu_i < temp
                solver.push()
                solver.add(expression)
                if MSIZE:
                    if check_sat(solver) != unsat:
                        # this means that it is possibly that current_miu_i < temp
                        current_miu_i = If(expression,temp,current_miu_i)
                solver.pop()
                mem.clear()  # very conservative
                mem[str(stored_address)] = stored_value
            state.miu_i = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MSTORE8":
        if len(stack) > 1:
            state.pc += 1
            stored_address = stack.pop(0)
            temp_value = stack.pop(0)
            stored_value = temp_value % 256  # get the least byte
            current_miu_i = state.miu_i
            if isAllReal(stored_address, current_miu_i):
                if six.PY2:
                    temp = long(math.ceil((stored_address + 1) / float(32)))
                else:
                    temp = int(math.ceil((stored_address + 1) / float(32)))
                if temp > current_miu_i:
                    current_miu_i = temp
                mem[stored_address] = stored_value  # note that the stored_value could be symbolic
            else:
                temp = (stored_address / 32) + 1
                if isReal(current_miu_i):
                    current_miu_i = BitVecVal(current_miu_i, 256)
                expression = current_miu_i < temp
                solver.push()
                solver.add(expression)
                if MSIZE:
                    if check_sat(solver) != unsat:
                        # this means that it is possibly that current_miu_i < temp
                        current_miu_i = If(expression,temp,current_miu_i)
                solver.pop()
                mem.clear()  # very conservative
                mem[str(stored_address)] = stored_value
            state.miu_i = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SLOAD":
        if len(stack) > 0:
            state.pc += 1
            position = stack.pop(0)
            if isReal(position) and position in state.Ia:
                value = state.Ia[position]
                stack.insert(0, value)
            #elif global_params.USE_GLOBAL_STORAGE and isReal(position) and position not in global_state["Ia"]:
            #    value = data_source.getStorageAt(position)
            #    global_state["Ia"][position] = value
            #    stack.insert(0, value)
            else:
                if str(position) in state.Ia:
                    value = state.Ia[str(position)]
                    stack.insert(0, value)
                else:
                    if is_expr(position):
                        position = simplify(position)
                    #if g_src_map:
                    #    new_var_name = g_src_map.get_source_code(global_state['pc'] - 1)
                    #    operators = '[-+*/%|&^!><=]'
                    #    new_var_name = re.compile(operators).split(new_var_name)[0].strip()
                    #    new_var_name = g_src_map.get_parameter_or_state_var(new_var_name)
                    #    if new_var_name:
                    #        new_var_name = gen.gen_owner_store_var(position, new_var_name)
                    #    else:
                    #        new_var_name = gen.gen_owner_store_var(position)
                    #else:
                    new_var_name = gen.gen_owner_store_var(position)

                    if new_var_name in variables:
                        new_var = variables[new_var_name]
                    else:
                        new_var = BitVec(new_var_name, 256)
                        variables[new_var_name] = new_var
                    stack.insert(0, new_var)
                    if isReal(position):
                        state.Ia[position] = new_var
                    else:
                        state.Ia[str(position)] = new_var
        else:
            raise ValueError('STACK underflow')

    elif opcode == "SSTORE":
        if len(stack) > 1:
            # for call_pc in calls:
            #     calls_affect_state[call_pc] = True
            state.pc += 1
            stored_address = stack.pop(0)
            stored_value = stack.pop(0)
            if isReal(stored_address):
                # note that the stored_value could be unknown
                state.Ia[stored_address] = stored_value
            else:
                # note that the stored_value could be unknown
                state.Ia[str(stored_address)] = stored_value
        else:
            raise ValueError('STACK underflow')
    elif opcode == "JUMP":
        if len(stack) > 0:
            target_address = stack.pop(0)
            if isSymbolic(target_address):
                try:
                    target_address = int(str(simplify(target_address)))
                except:
                    raise TypeError("Target address must be an integer")
            return target_address
        else:
            raise ValueError('STACK underflow')
    elif opcode == "JUMPI":
        # We need to prepare two branches
        if len(stack) > 1:
            target_address = stack.pop(0)
            if isSymbolic(target_address):
                try:
                    target_address = int(str(simplify(target_address)))
                except:
                    raise TypeError("Target address must be an integer")
            flag = stack.pop(0)
            branch_expression = (BitVecVal(0, 1) == BitVecVal(1, 1))
            if isReal(flag):
                if flag != 0:
                    branch_expression = True
            else:
                branch_expression = (flag != 0)

            # expr here
            branch_expr = branch_expression

            return target_address

        else:
            raise ValueError('STACK underflow')

    elif opcode == "PC":
        stack.insert(0, state.pc)
        state.pc += 1
    elif opcode == "MSIZE":
        state.pc += 1
        msize = 32 * state.miu_i
        stack.insert(0, msize)
    elif opcode == "GAS":
        # In general, we do not have this precisely. It depends on both
        # the initial gas and the amount has been depleted
        # we need o think about this in the future, in case precise gas
        # can be tracked
        state.pc += 1
        new_var_name = gen.gen_gas_var()
        new_var = BitVec(new_var_name, 256)
        variables[new_var_name] = new_var
        stack.insert(0, new_var)
    elif opcode == "JUMPDEST":
        # Literally do nothing
        state.pc += 1
    #
    #  60s & 70s: Push Operations
    #
    elif opcode.startswith('PUSH', 0):  # this is a push instruction
        position = int(opcode[4:], 10)
        state.pc += 1 + position
        pushed_value = instr.operand
        stack.insert(0, pushed_value)
        # if global_params.UNIT_TEST == 3: # test evm symbolic
        #     stack[0] = BitVecVal(stack[0], 256)
    #
    #  80s: Duplication Operations
    #
    elif opcode.startswith("DUP", 0):
        state.pc += 1
        position = int(opcode[3:], 10) - 1
        if len(stack) > position:
            duplicate = stack[position]
            stack.insert(0, duplicate)
        else:
            raise ValueError('STACK underflow')

    #
    #  90s: Swap Operations
    #
    elif opcode.startswith("SWAP", 0):
        state.pc += 1
        position = int(opcode[4:], 10)
        if len(stack) > position:
            temp = stack[position]
            stack[position] = stack[0]
            stack[0] = temp
        else:
            raise ValueError('STACK underflow')

    #
    #  a0s: Logging Operations
    #
    elif opcode in ("LOG0", "LOG1", "LOG2", "LOG3", "LOG4"):
        state.pc += 1
        # We do not simulate these log operations
        num_of_pops = 2 + int(opcode[3:])
        while num_of_pops > 0:
            stack.pop(0)
            num_of_pops -= 1

    #
    #  f0s: System Operations
    #
    elif opcode == "CREATE":
        if len(stack) > 2:
            state.pc += 1
            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
            new_var_name = gen.gen_arbitrary_var()
            new_var = BitVec(new_var_name, 256)
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CALL":
        # TODO: Need to handle miu_i
        if len(stack) > 6:
            # calls.append(state.pc)
            # for call_pc in calls:
            #     if call_pc not in calls_affect_state:
            #         calls_affect_state[call_pc] = False
            state.pc += 1
            outgas = stack.pop(0)
            recipient = stack.pop(0)
            transfer_amount = stack.pop(0)
            start_data_input = stack.pop(0)
            size_data_input = stack.pop(0)
            start_data_output = stack.pop(0)
            size_data_ouput = stack.pop(0)
            # in the paper, it is shaky when the size of data output is
            # min of stack[6] and the | o |

            if isReal(transfer_amount):
                if transfer_amount == 0:
                    stack.insert(0, 1)   # x = 0
                    return

            # Let us ignore the call depth
            balance_ia = state.balance["Ia"]
            is_enough_fund = (transfer_amount <= balance_ia)
            solver.push()
            solver.add(is_enough_fund)

            if check_sat(solver) == unsat:
                # this means not enough fund, thus the execution will result in exception
                solver.pop()
                stack.insert(0, 0)   # x = 0
            else:
                # the execution is possibly okay
                stack.insert(0, 1)   # x = 1
                solver.pop()
                solver.add(is_enough_fund)
                state.constraints.append(is_enough_fund)
                last_idx = len(state.constraints) - 1
                new_balance_ia = (balance_ia - transfer_amount)
                state.balance["Ia"] = new_balance_ia
                address_is = variables["Is"]
                address_is = (address_is & CONSTANT_ONES_159)
                boolean_expression = (recipient != address_is)
                solver.push()
                solver.add(boolean_expression)
                if check_sat(solver) == unsat:
                    solver.pop()
                    new_balance_is = (state.balance["Is"] + transfer_amount)
                    state.balance["Is"] = new_balance_is
                else:
                    solver.pop()
                    if isReal(recipient):
                        new_address_name = "concrete_address_" + str(recipient)
                    else:
                        new_address_name = gen.gen_arbitrary_address_var()
                    old_balance_name = gen.gen_arbitrary_var()
                    old_balance = BitVec(old_balance_name, 256)
                    variables[old_balance_name] = old_balance
                    constraint = (old_balance >= 0)
                    solver.add(constraint)
                    state.constraints.append(constraint)
                    new_balance = (old_balance + transfer_amount)
                    state.balance[new_address_name] = new_balance
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CALLCODE":
        # TODO: Need to handle miu_i
        if len(stack) > 6:
            #calls.append(global_state["pc"])
            #for call_pc in calls:
            #    if call_pc not in calls_affect_state:
            #        calls_affect_state[call_pc] = False
            state.pc += 1
            outgas = stack.pop(0)
            recipient = stack.pop(0) # this is not used as recipient
            # if global_params.USE_GLOBAL_STORAGE:
            #     if isReal(recipient):
            #         recipient = hex(recipient)
            #         if recipient[-1] == "L":
            #             recipient = recipient[:-1]
            #         recipients.add(recipient)
            #     else:
            #         recipients.add(None)

            transfer_amount = stack.pop(0)
            start_data_input = stack.pop(0)
            size_data_input = stack.pop(0)
            start_data_output = stack.pop(0)
            size_data_ouput = stack.pop(0)
            # in the paper, it is shaky when the size of data output is
            # min of stack[6] and the | o |

            if isReal(transfer_amount):
                if transfer_amount == 0:
                    stack.insert(0, 1)   # x = 0
                    return

            # Let us ignore the call depth
            balance_ia = state.balance["Ia"]
            is_enough_fund = (transfer_amount <= balance_ia)
            solver.push()
            solver.add(is_enough_fund)

            if check_sat(solver) == unsat:
                # this means not enough fund, thus the execution will result in exception
                solver.pop()
                stack.insert(0, 0)   # x = 0
            else:
                # the execution is possibly okay
                stack.insert(0, 1)   # x = 1
                solver.pop()
                solver.add(is_enough_fund)
                state.constraints.append(is_enough_fund)
                last_idx = len(state.constraints) - 1
        else:
            raise ValueError('STACK underflow')
    elif opcode in ("DELEGATECALL", "STATICCALL"):
        if len(stack) > 5:
            state.pc += 1
            stack.pop(0)
            recipient = stack.pop(0)
            # if global_params.USE_GLOBAL_STORAGE:
            #     if isReal(recipient):
            #         recipient = hex(recipient)
            #         if recipient[-1] == "L":
            #             recipient = recipient[:-1]
            #         recipients.add(recipient)
            #     else:
            #         recipients.add(None)

            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
            new_var_name = gen.gen_arbitrary_var()
            new_var = BitVec(new_var_name, 256)
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode in ("RETURN", "REVERT"):
        # TODO: Need to handle miu_i
        if len(stack) > 1:
            if opcode == "REVERT":
                state.pc += 1
            stack.pop(0)
            stack.pop(0)
            # TODO
            pass
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SUICIDE":
        state.pc += 1
        recipient = stack.pop(0)
        transfer_amount = state.balance["Ia"]
        state.balance["Ia"] = 0
        if isReal(recipient):
            new_address_name = "concrete_address_" + str(recipient)
        else:
            new_address_name = gen.gen_arbitrary_address_var()
        old_balance_name = gen.gen_arbitrary_var()
        old_balance = BitVec(old_balance_name, 256)
        variables[old_balance_name] = old_balance
        constraint = (old_balance >= 0)
        solver.add(constraint)
        state.constraints.append(constraint)
        new_balance = (old_balance + transfer_amount)
        state.balance[new_address_name] = new_balance
        # TODO
        return

    else:
        print("UNKNOWN INSTRUCTION: " + opcode)
        # if global_params.UNIT_TEST == 2 or global_params.UNIT_TEST == 3:
        #     log.critical("Unknown instruction: %s" % opcode)
        #     exit(UNKNOWN_INSTRUCTION)
        raise Exception('UNKNOWN INSTRUCTION: ' + opcode)



