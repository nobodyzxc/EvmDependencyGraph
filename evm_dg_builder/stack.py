import itertools

def rm_dup(seq):
    seen = set()
    return [x for x in seq if not (x in seen or seen.add(x))]

class AbsStackElem(object):
    '''
        Represent an element of the stack
        An element is a set of potential values.
        There are at max MAXVALS number of values, otherwise it is set to TOP

        TOP is representented as None

        []     --> [1, 2, None, 3...]  --> None
        Init   --> [ up to 10 vals ]   --  TOP

        If a value is not known, it is None.
        Note that we make the difference between the list beeing TOP, and one
        of the value inside the list beeing TOP. The idea is that even if one
        of the value is not known, we can list keep track of the known values.

        Thus our analysis is an under-approximation of an over-approximation
        and is not sound.
    '''

    # Maximum number of values inside the set. If > MAXVALS -> TOP
    MAXVALS = 100

    def __init__(self):
        self._vals = []

    def append(self, nbr):
        '''
            Append value to the element

        Args:
            nbr (int, long, binaryninja.function.InstructionTextToken, None)
        '''
        if nbr is None:
            self._vals.append(None)
        else:
            self._vals.append(nbr)

    def get_vals(self):
        '''
            Return the values. The return must be checked for TOP (None)

        Returns:
            list of int, or None
        '''
        return self._vals

    def set_vals(self, vals):
        '''
            Set the values
        Args:
            vals (list of int, or None): List of values, or TOP
        '''
        self._vals = vals

    def absAnd(self, elem):
        '''
            AND between two AbsStackElem
        Args:
            elem (AbsStackElem)
        Returns:
            AbsStackElem: New object containing the result of the AND between
            the values. If one of the absStackElem is TOP, returns TOP
        '''
        newElem = AbsStackElem()
        v1 = self.get_vals()
        v2 = elem.get_vals()
        if not v1 or not v2:
            newElem.set_vals(None)
            return newElem

        for (a, b) in itertools.product(v1, v2):
            if a is None or b is None:
                newElem.append(None)
            else:
                newElem.append(a & b)

        return newElem

    def merge(self, elem):
        '''
            Merge between two AbsStackElem
        Args:
            elem (AbsStackElem)
        Returns:
            AbsStackElem: New object containing the result of the merge
                          If one of the absStackElem is TOP, returns TOP
        '''
        newElem = AbsStackElem()
        v1 = self.get_vals()
        v2 = elem.get_vals()
        if not v1 or not v2:
            newElem.set_vals(None)
            return newElem

        # vals = list(set(v1 + v2))
        vals = rm_dup(v1 + v2)

        if len(vals) > self.MAXVALS:
            vals = None
        newElem.set_vals(vals)
        return newElem

    def equals(self, elems):
        '''
            Return True if equal

        Args:
            elem (AbsStackElem)
        Returns:
            bool: True if the two absStackElem are equals. If both are TOP
            returns True
        '''

        v1 = self.get_vals()

        v2 = elems.get_vals()

        if not v1 or not v2:
            if not v1 and not v2:
                return True
            return False

        if len(v1) != len(v2):
            return False

        if any(v not in v2 for v in v1):
            return False

        return True

    def get_copy(self):
        '''
            Return of copy of the object
        Returns:
            AbsStackElem
        '''
        cp = AbsStackElem()
        cp.set_vals(self.get_vals())
        return cp

    def __str__(self):
        '''
            String representation
        Returns:
            str
        '''
        return str(self._vals)


class AbstStack(object):
    '''
        Stack representation
        The stack is updated throyugh the push/pop/dup operation, and returns
        itself
        We keep the same stack for one basic block, to reduce the memory usage
    '''

    def __init__(self):
        self._elems = []

    def copy_stack(self, stack):
        '''
            Copy the given stack

        Args:
            Stack: stack to copy
        '''
        self._elems = [x.get_copy() for x in stack.get_elems()]
        return self

    def push(self, elem):
        '''
            Push an elem. If the elem is not an AbsStackElem, create a new
            AbsStackElem
        Args:
            elem (AbsStackElem, or str or None): If str, it should be the
            hexadecimal repr
        '''
        if not isinstance(elem, AbsStackElem):
            st = AbsStackElem()
            st.append(elem)
            elem = st

        self._elems.append(elem)

    def insert(self, elem):
        if not isinstance(elem, AbsStackElem):
            st = AbsStackElem()
            st.append(elem)
            elem = st

        self._elems.insert(0, elem)

    def pop(self):
        '''
            Pop an element.
        Returns:
            AbsStackElem
        '''
        if not self._elems:
            self.push(None)

        return self._elems.pop()

    def swap(self, n):
        '''
            Swap operation
        Args:
            n (int)
        '''
        if len(self._elems) >= (n+1):
            elem = self._elems[-1-n]
            top = self.top()
            self._elems[-1] = elem
            self._elems[-1-n] = top

        # if we swap more than the size of the stack,
        # we can assume that elements are missing on the stack
        else:
            top = self.top()
            missing_elems = n - len(self._elems) + 1
            for _ in range(0, missing_elems):
                self.insert(None)
            self._elems[-1-n] = top

    def dup(self, n):
        '''
            Dup operation
        '''
        if len(self._elems) >= n:
            self.push(self._elems[-n])
        else:
            self.push(None)

    def get_elems(self):
        '''
            Returns the stack elements
        Returns:
            List AbsStackElem
        '''
        return self._elems

    def set_elems(self, elems):
        '''
            Set the stack elements
        Args:
            elems (list of AbsStackElem)
        '''
        self._elems = elems

    def merge(self, stack):
        '''
            Merge two stack. Returns a new object
        Arg:
            stack (Stack)
        Returns: New object representing the merge
        '''
        newSt = Stack()
        elems1 = self.get_elems()
        elems2 = stack.get_elems()
        # We look for the longer stack
        if len(elems2) <= len(elems1):
            longStack = elems1
            shortStack = elems2
        else:
            longStack = elems2
            shortStack = elems1
        longStack = [x.get_copy() for x in longStack]
        # Merge elements
        for i in range(0, len(shortStack)):
            longStack[-(i+1)] = longStack[-(i+1)].merge(shortStack[-(i+1)])
        newSt.set_elems(longStack)

        return newSt

    def equals(self, stack):
        '''
            Test equality between two stack
        Args:
            stack (Stack)
        Returns:
            bool: True if the stac are equals
        '''
        elems1 = self.get_elems()
        elems2 = stack.get_elems()
        if len(elems1) != len(elems2):
            return False
        for (v1, v2) in zip(elems1, elems2):
            if not v1.equals(v2):
                return False
        return True

    def top(self):
        '''
            Return the element at the top (without pop)
        Returns:
            AbsStackElem
        '''
        if not self._elems:
            self.push(None)
        return self._elems[-1]

    def __str__(self):
        '''
            String representation (only first 5 items)
        '''
        return str([str(x) for x in self._elems[-100::]])


class ListStack(object):
    '''
        Stack representation
        The stack is updated throyugh the push/pop/dup operation, and returns
        itself
        We keep the same stack for one basic block, to reduce the memory usage
    '''

    def __init__(self):
        self._insts = [[]]

    def copy_stack(self, stack):
        '''
            Copy the given stack

        Args:
            Stack: stack to copy
        '''
        self._insts = [x.copy() for x in stack.get_insts()]
        return self

    def push(self, inst):
        #if not isinstance(inst, AbsStackElem):
        #    st = AbsStackElem()
        #    st.append(inst)
        #    inst = st
        for i, s in enumerate(self._insts):
            self._insts[i].append(inst)

    def insert(self, inst):
        #if not isinstance(inst, AbsStackElem):
        #    st = AbsStackElem()
        #    st.append(inst)
        #    inst = st

        for i, s in enumerate(self._insts):
            self._insts[i].insert(0, inst)

    def pop(self):

        for i, s in enumerate(self._insts):
            if not self._insts[i]:
                self._insts[i].append(None)
        return [self._insts[i].pop() for i, s in enumerate(self._insts)]

    def ipopOf(self, idx):

        if not self._insts[idx]:
            self._insts[idx].append(None)
        return self._insts[idx].pop()

    def swap(self, n):
        '''
            Swap operation
        Args:
            n (int)
        '''
        for i, s in enumerate(self._insts):
            if len(self._insts[i]) >= (n+1):
                inst = self._insts[i][-1-n]
                top = self.topOf(i)
                self._insts[i][-1] = inst
                self._insts[i][-1-n] = top

            # if we swap more than the size of the stack,
            # we can assume that elements are missing on the stack
            else:
                top = self.topOf(i)
                missing_insts = n - len(self._insts[i]) + 1
                for _ in range(0, missing_insts):
                    self.insert(None)
                self._insts[i][-1-n] = top

    def dup(self, n):

        for i, s in enumerate(self._insts):
            if len(self._insts[i]) >= n:
                self._insts[i].append(self._insts[i][-n])
            else:
                self._insts[i].append(None)

    def get_insts(self):
        return self._insts

    def set_insts(self, insts):
        self._insts = insts
        return self

    def merge(self, stack):
        return ListStack().set_insts(
                [x.copy() for x in self.get_insts()] + \
                [x.copy() for x in stack.get_insts()])

    def equals(self, stack):
        insts1 = self.get_insts()
        insts2 = stack.get_insts()
        if len(insts1) != len(insts2):
            return False
        for (v1, v2) in zip(insts1, insts2):
            if not v1.equals(v2):
                return False
        return True

    def topOf(self, idx):

        if not self._insts[idx]:
            self._insts[idx].append(None)

        return self._insts[idx][-1]



    def top(self):
        '''
            Return the element at the top (without pop)
        Returns:
            AbsStackElem
        '''
        for i, s in enumerate(self._insts):
            if not self._insts[i]:
                self._insts[i].append(None)

        return [s[-1] for s in self._insts]

    def __str__(self):
        '''
            String representation (only first 5 items)
        '''
        return str([str(x) for x in self._insts[-100::]])

