from opcode import *

def calculate_gas(opcode, state, solver):

    stack = state.stack

    gas_constraints = ""

    gas_increment = get_ins_cost(opcode) # base cost

    if opcode in ("LOG0", "LOG1", "LOG2", "LOG3", "LOG4") \
            and len(stack) > 1:
        if isReal(stack[1]):
            gas_increment += GCOST["Glogdata"] * stack[1]
        elif isinstance(stack[1], BitVecRef):
            # upper bound if unknown
            gas_increment += GCOST["Glogdata"] * (2 ** 256)
            gas_constraints = \
                    "{}(Glogdata) * 2^256:(){}".format(
                    GCOST["Glogdata"],
                    "{ " + str(stack[1]) + " : 2^256 }")
        else:
            print("unknown type on LOG", type(stack[1]))
            exit(0)
    elif opcode == "EXP" and len(stack) > 1:
        if isReal(stack[1]):
            if stack[1] > 0:
                # EXP ESTIMATION HERE
                gas_increment += GCOST["Gexpbyte"] * (1 + math.floor(math.log(stack[1], 256)))
        elif isinstance(stack[1], BitVecRef):
            # upper bound if unknown
            gas_increment += GCOST["Gexpbyte"] * 33
            gas_constraints = \
                    "{}(Gexpbyte) * 33:({} > 0){}".format(
                    GCOST["Gexpbyte"],
                    str(stack[1]),
                    "{ " + str(stack[1]) + " : 2^256 }")
        else:
            print("unknown type on EXP", type(stack[1]))
            exit(0)
    elif opcode == "EXTCODECOPY" and len(stack) > 3:
        # oyente ERROR to be 2
        # fix to 3 according to spec
        if isReal(stack[3]):
            gas_increment += GCOST["Gcopy"] * math.ceil(stack[3] / 32)
        elif isinstance(stack[3], BitVecRef):
            # upper bound if unknown
            gas_increment += GCOST["Gcopy"] * (2 ** 251)
            gas_constraints = "{}(Gcopy) * 2^251:(){}".format(
                    GCOST["Gcopy"], "{ " + str(stack[3]) + " : 2^256 }")
        else:
            print("unknown type on EXTCODECOPY", type(stack[3]))
            exit(0)
    elif opcode in ("CALLDATACOPY", "CODECOPY", "RETURNDATACOPY") and len(stack) > 2:
        if isReal(stack[2]):
            # oyente ERROR to be 3
            # fix to 3 according to spec
            gas_increment += GCOST["Gcopy"] * math.ceil(stack[2] / 32)
        elif isinstance(stack[2], BitVecRef):
            # upper bound if unknown
            gas_increment += GCOST["Gcopy"] * (2 ** 251)
            gas_constraints = \
                    "{}(Gcopy) * 2^251:(){}".format(
                    GCOST["Gcopy"],
                    "{ " + str(stack[2]) + " : 2^256 }")
        else:
            print("unknown type on CALLDATACOPY || CODECOPY",
                    type(stack[2]))
            exit(0)
    elif opcode == "SSTORE" and len(stack) > 1:
        if isReal(stack[1]):
            try:
                try:
                    storage_value = state.Ia[int(stack[0])]
                except:
                    storage_value = state.Ia[str(stack[0])]
                # when we change storage value from zero to non-zero
                if storage_value == 0 and stack[1] != 0:
                    gas_increment += GCOST["Gsset"]
                else:
                    gas_increment += GCOST["Gsreset"]
            except: # when storage address at considered key is empty
                if stack[1] != 0:
                    gas_increment += GCOST["Gsset"]
                elif stack[1] == 0:
                    gas_increment += GCOST["Gsreset"]
        else:
            #print("SSOTRE WITH ", stack[0], stack[1])
            #input("any key to continue(not real) >> ")
            try:
                try:
                    storage_value = state.Ia[int(stack[0])]
                except:
                    storage_value = state.Ia[str(stack[0])]
                solver.push()
                solver.add(And(storage_value == 0, stack[1] != 0))
                expr = "{} == 0 \n&& {} != 0\n? {} : {})".format(
                        str(storage_value), str(stack[1]),
                        str(GCOST["Gsset"]), str(GCOST["Gsreset"]))
                if solver.check() == sat:
                    gas_increment += GCOST["Gsset"]
                    gas_constraints += "{}(Gsset):({}){}".format(
                            GCOST["Gsset"], expr,
                            pprint.pformat(solver.model())\
                                    .replace("[", "{")\
                                    .replace("]", "}")\
                                    .replace("=", ":"))
                elif solver.check() == unsat:
                    gas_increment += GCOST["Gsreset"]
                    gas_constraints += "{}(Gsreset):({}){}".format(
                            GCOST["Gsreset"], expr, "{unsat}")

                else:# check == unknown
                    gas_increment += GCOST["Gsset"]
                    gas_constraints += "{}(Gsset):({}){}".format(
                            GCOST["Gsset"], expr, "{unknown}")
                solver.pop()
            except Exception as e:
                if str(e) == "canceled":
                    solver.pop()
                solver.push()
                solver.add(stack[1] != 0)
                expr = "{} != 0 ? {} : {}".format(
                        str(stack[1]), GCOST["Gsset"], GCOST["Gsreset"])
                state = solver.check()
                if state == sat:
                    gas_increment += GCOST["Gsset"]
                    gas_constraints += "{}(Gsset):({}){}".format(
                            GCOST["Gsset"], expr,
                            pprint.pformat(solver.model())\
                                    .replace("[", "{")\
                                    .replace("]", "}")\
                                    .replace("=", ":"))
                elif state == unsat:
                    gas_increment += GCOST["Gsreset"]
                    gas_constraints += "{}(Gsreset):({}){}".format(
                            GCOST["Gsreset"], expr, "{unsat}")
                else: # unknown
                    gas_increment += GCOST["Gsset"]
                    gas_constraints += "{}(Gsset):({}){}".format(
                            GCOST["Gsset"], expr, "{unknown}")
                solver.pop()
    elif opcode in ("SUICIDE", "SELFDESTRUCT") \
            and len(stack) > 1:
        if isReal(stack[1]):
            address = stack[1] % 2**160
            if address not in global_state:
                gas_increment += GCOST["Gnewaccount"]
        else:
            address = str(stack[1])
            if address not in global_state:
                gas_increment += GCOST["Gnewaccount"]
    elif opcode in ("CALL", "CALLCODE", "DELEGATECALL") \
            and len(stack) > 2:
        # Not fully correct yet
        gas_increment += GCOST["Gcall"]
        if isReal(stack[2]):
            if stack[2] != 0:
                gas_increment += GCOST["Gcallvalue"]
        else:
            solver.push()
            solver.add(stack[2] != 0)

            expr = "{} != 0 ? {} : 0".format(
                    str(stack[2]), GCOST["Gcallvalue"])

            state = check_sat(solver)
            if state == sat:
                gas_increment += GCOST["Gcallvalue"]
                gas_constraints += \
                        "{}(Gcallvalue):({}){}".format(
                                GCOST["Gcallvalue"], expr,
                                pprint.pformat(solver.model())\
                                .replace("[", "{")\
                                .replace("]", "}")\
                                .replace("=", ":"))
            elif state == unsat:
                gas_constraints += "0:({}){}".format(
                        expr, "{unsat}")
            else: # unknown
                gas_increment += GCOST["Gcallvalue"]
                gas_constraints += \
                        "{}(Gcallvalue):({}){}".format(
                        GCOST["Gcallvalue"], expr, "{unknown}")

            solver.pop()

    elif opcode == "SHA3":
        # pass # Not handle => try to handle
        if isReal(stack[1]):
            gas_increment += GCOST["Gsha3word"] * math.ceil(stack[1] / 32)
        elif isinstance(stack[1], BitVecRef):
            # upper bound if unknown
            gas_increment += GCOST["Gsha3word"] * (2 ** 251)
            gas_constraints = \
                    "{}(Gsha3) + {}(Gsha3word) * 2^251:(){}"\
                    .format(GCOST["Gsha3"],
                            GCOST["Gsha3word"],
                            "{ " + str(stack[1]) + ": 2^256 }")
        else:
            print("unknown type on SHA3", type(stack[1]))
            exit(0)

    return (gas_increment, gas_constraints)


def calculate_mem_gas(state):
    #Calculate gas memory, add it to total gas used
    length = len(state.mem.keys()) # number of memory words
    return GCOST["Gmemory"] * length + (length ** 2) // 512
