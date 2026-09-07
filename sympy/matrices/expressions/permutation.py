from sympy.core import S, Tuple, Basic
from sympy.core.decorators import call_highest_priority
from sympy.core.sympify import _sympify
from sympy.functions import KroneckerDelta
from sympy.core.cache import cacheit

from .matexpr import MatrixExpr, ConstantMatrix, Identity, Zeros, Ones, _sympifyit


class PermutationMatrix(MatrixExpr):
    """A Permutation Matrix

    Parameters
    ==========

    perm : Permutation
        The permutation the matrix uses.

        The size of the permutation determines the matrix size.

        See the documentation of
        :class:`sympy.combinatorics.permutations.Permutation` for
        the further information of how to create a permutation object.

    Examples
    ========

    >>> from sympy.matrices import Matrix, PermutationMatrix
    >>> from sympy.combinatorics import Permutation

    Creating a permutation matrix:

    >>> p = Permutation(1, 2, 0)
    >>> P = PermutationMatrix(p)
    >>> P = P.as_explicit()
    >>> P
    Matrix([
    [0, 1, 0],
    [0, 0, 1],
    [1, 0, 0]])

    Permuting a matrix row and column:

    >>> M = Matrix([0, 1, 2])
    >>> Matrix(P*M)
    Matrix([
    [1],
    [2],
    [0]])

    >>> Matrix(M.T*P)
    Matrix([[2, 0, 1]])

    See Also
    ========

    sympy.combinatorics.permutations.Permutation
    """

    def __new__(cls, perm):
        from sympy.combinatorics.permutations import Permutation

        perm = _sympify(perm)
        if not isinstance(perm, Permutation):
            raise ValueError(
                "{} must be a SymPy Permutation instance.".format(perm))

        return super().__new__(cls, perm)

    @cacheit
    def _eval_shape(self):
        size = self.args[0].size
        return (size, size)

    @property
    def is_Identity(self):
        return self.args[0].is_Identity

    def doit(self):
        if self.is_Identity:
            return Identity(self.rows)
        return self

    def _entry(self, i, j, **kwargs):
        perm = self.args[0]
        return KroneckerDelta(perm.apply(i), j)

    def _eval_power(self, exp):
        return PermutationMatrix(self.args[0] ** exp).doit()

    def _eval_inverse(self):
        return PermutationMatrix(self.args[0] ** -1)

    _eval_transpose = _eval_adjoint = _eval_inverse

    def _eval_determinant(self, **kwargs):
        sign = self.args[0].signature()
        if sign == 1:
            return S.One
        elif sign == -1:
            return S.NegativeOne
        raise NotImplementedError

    def _eval_rewrite_as_BlockDiagMatrix(self, *args, **kwargs):
        from sympy.combinatorics.permutations import Permutation
        from .blockmatrix import BlockDiagMatrix

        perm = self.args[0]
        full_cyclic_form = perm.full_cyclic_form

        cycles_picks = []

        # Stage 1. Decompose the cycles into the blockable form.
        a, b, c = 0, 0, 0
        flag = False
        for cycle in full_cyclic_form:
            l = len(cycle)
            m = max(cycle)

            if not flag:
                if m + 1 > a + l:
                    flag = True
                    temp = [cycle]
                    b = m
                    c = l
                else:
                    cycles_picks.append([cycle])
                    a += l

            else:
                if m > b:
                    if m + 1 == a + c + l:
                        temp.append(cycle)
                        cycles_picks.append(temp)
                        flag = False
                        a = m+1
                    else:
                        b = m
                        temp.append(cycle)
                        c += l
                else:
                    if b + 1 == a + c + l:
                        temp.append(cycle)
                        cycles_picks.append(temp)
                        flag = False
                        a = b+1
                    else:
                        temp.append(cycle)
                        c += l

        # Stage 2. Normalize each decomposed cycles and build matrix.
        p = 0
        args = []
        for pick in cycles_picks:
            new_cycles = []
            l = 0
            for cycle in pick:
                new_cycle = [i - p for i in cycle]
                new_cycles.append(new_cycle)
                l += len(cycle)
            p += l
            perm = Permutation(new_cycles)
            mat = PermutationMatrix(perm)
            args.append(mat)

        return BlockDiagMatrix(*args)


class MatrixPermute(MatrixExpr):
    r"""Symbolic representation for permuting matrix rows or columns.

    Parameters
    ==========

    perm : Permutation, PermutationMatrix
        The permutation to use for permuting the matrix.
        The permutation can be resized to the suitable one,

    axis : 0 or 1
        The axis to permute alongside.
        If `0`, it will permute the matrix rows.
        If `1`, it will permute the matrix columns.

    Notes
    =====

    This follows the same notation used in
    :meth:`sympy.matrices.common.MatrixCommon.permute`.

    Examples
    ========

    >>> from sympy.matrices import Matrix, MatrixPermute
    >>> from sympy.combinatorics import Permutation

    Permuting the matrix rows:

    >>> p = Permutation(1, 2, 0)
    >>> A = Matrix([[1, 2, 3], [4, 5, 6], [7, 8, 9]])
    >>> B = MatrixPermute(A, p, axis=0)
    >>> B.as_explicit()
    Matrix([
    [4, 5, 6],
    [7, 8, 9],
    [1, 2, 3]])

    Permuting the matrix columns:

    >>> B = MatrixPermute(A, p, axis=1)
    >>> B.as_explicit()
    Matrix([
    [2, 3, 1],
    [5, 6, 4],
    [8, 9, 7]])

    See Also
    ========

    sympy.matrices.common.MatrixCommon.permute
    """
    def __new__(cls, mat, perm, axis=S.Zero):
        from sympy.combinatorics.permutations import Permutation

        mat = _sympify(mat)
        if not mat.is_Matrix:
            raise ValueError(
                "{} must be a SymPy matrix instance.".format(perm))

        perm = _sympify(perm)
        if isinstance(perm, PermutationMatrix):
            perm = perm.args[0]

        if not isinstance(perm, Permutation):
            raise ValueError(
                "{} must be a SymPy Permutation or a PermutationMatrix " \
                "instance".format(perm))

        axis = _sympify(axis)
        if axis not in (0, 1):
            raise ValueError("The axis must be 0 or 1.")

        mat_size = mat.shape[axis]
        if mat_size != perm.size:
            try:
                perm = perm.resize(mat_size)
            except ValueError:
                raise ValueError(
                    "Size does not match between the permutation {} "
                    "and the matrix {} threaded over the axis {} "
                    "and cannot be converted."
                    .format(perm, mat, axis))

        return super().__new__(cls, mat, perm, axis)

    def doit(self, deep=True):
        mat, perm, axis = self.args

        if deep:
            mat = mat.doit(deep=deep)
            perm = perm.doit(deep=deep)

        if perm.is_Identity:
            return mat

        if mat.is_Identity:
            if axis is S.Zero:
                return PermutationMatrix(perm)
            elif axis is S.One:
                return PermutationMatrix(perm**-1)

        if isinstance(mat, (Zeros, Ones)):
            return mat

        if isinstance(mat, MatrixPermute) and mat.args[2] == axis:
            return MatrixPermute(mat.args[0], perm * mat.args[1], axis)

        return self

    @cacheit
    def _eval_shape(self):
        return self.args[0].shape

    def _entry(self, i, j, **kwargs):
        mat, perm, axis = self.args

        if axis == 0:
            return mat[perm.apply(i), j]
        elif axis == 1:
            return mat[i, perm.apply(j)]

    def _eval_rewrite_as_MatMul(self, *args, **kwargs):
        from .matmul import MatMul

        mat, perm, axis = self.args

        deep = kwargs.get("deep", True)

        if deep:
            mat = mat.rewrite(MatMul)

        if axis == 0:
            return MatMul(PermutationMatrix(perm), mat)
        elif axis == 1:
            return MatMul(mat, PermutationMatrix(perm**-1))


class ElementaryMatrix(ConstantMatrix):
    
    @property
    def rows(self):
        return self.shape[-1]

    @property
    def cols(self):
        return self.shape[-2]

    @property
    def n(self):
        return self.shape[-1]
    
    def _eval_is_extended_integer(self):
        return True
    
    def _eval_is_finite(self):
        return True
     
    def _eval_is_singular(self):
        return False
    
    def _eval_is_extended_negative(self):
        return False
    
    def _latex(self, p):
        return Basic._latex(self, p)
    
    def _sympystr(self, p):
        return Basic._sympystr(self, p)
    
    def _lean(self, p):
        return Basic._sympystr(self, p)
    
    @property
    def is_square(self):
        return True
    
    def conjugate(self):
        return self
    

# precondition: i > j or i < j
class SwapMatrix(ElementaryMatrix, MatrixExpr):
    
    def __new__(cls, *args, **kwargs):
        shape = kwargs.get('shape')
        if shape:
            n = shape[-1]
            i, j = args
        else:
            n, i, j = args
            
        n = _sympify(n)
        if i == j:
            return Identity(n)
        return MatrixExpr.__new__(cls, i, j, shape=(n, n))
    
    def _entry(self, i, j=None, **_):
        from sympy import Stack, Piecewise, Equal
        if isinstance(i, Tuple):
            start, stop, step = i.slice_args
            if start == 0 and stop  == self.n and step == 1:
                i = self.generate_var(excludes=None if j is None else j.free_symbols, integer=True)
                return_reference_i = True
            else:
                raise Exception('general i slice unimplemented')
        else:
            return_reference_i = False
            
        if j is None:
            return_reference_j = True
            j = self.generate_var(excludes=i.free_symbols, integer=True)
        else:
            return_reference_j = False
        piecewise = Piecewise((KroneckerDelta(j, self.i), Equal(i, self.j)),
                              (KroneckerDelta(j, self.j), Equal(i, self.i)),
                              (KroneckerDelta(j, i), True))

        if return_reference_j:
            return Stack[j:self.n](piecewise)
        if return_reference_i:
            return Stack[i:self.n](piecewise)
        return piecewise

    @property
    def i(self):
        return self.args[0]

    @property
    def j(self):
        return self.args[1]

    def _eval_determinant(self, **kwargs):        
        return 2 * KroneckerDelta(self.i, self.j) - 1

    def _eval_transpose(self, *axis):
        if axis == self.default_axis: 
            return self

    def _eval_inverse(self):
        return self

    @property
    def is_upper(self):
        return self.i == self.j
    
    @property
    def is_lower(self):
        return self.i == self.j

    @cacheit
    def _eval_domain_defined(self, x, **_): 
        return self.n.domain_defined(x) & x.domain_conditioned((self.i < self.n) & (self.i >= 0) & ((self.j < self.n) & (self.j >= 0)))

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__rmatmul__')
    def __matmul__(self, other):
        if other.is_BlockMatrix:
            if other.axis == 0:
                other_i = other[self.i]
                other_j = other[self.j]
                
                try:
                    args = other.args
                    i_ = args.index(other_i)
                    j_ = args.index(other_j)
                    
                    args = [*args]
                    args[i_], args[j_] = args[j_], args[i_]
                    return other.func(*args)
                except ValueError:
                    return MatrixExpr.__matmul__(self, other)  
        elif other.is_DenseMatrix:
            rows = [other[i]._args for i in range(other.rows)]
            rows[self.i], rows[self.j] = rows[self.j], rows[self.i]
            
            return other.func(tuple(rows)).simplify()  
            
        return MatrixExpr.__matmul__(self, other)

    def _eval_trace(self):
        from sympy import Piecewise, Equal
        return Piecewise((self.rows, Equal(self.i, self.j)), (self.rows - 2, True))
    
    def _sympystr(self, p):
        n = self.shape[-1]
        i, j = self.args
        n = p._print(n)
        i = p._print(i)
        j = p._print(j)
        return f'SwapMatrix({n}, {i}, {j})'

    def _lean(self, p):
        n = self.shape[-1]
        i, j = self.args
        n = p._print(n)
        i = p._print(i)
        j = p._print(j)
        return f'SwapMatrix({n}, {i}, {j})'

class MulMatrix(ElementaryMatrix, MatrixExpr):

    _op_priority = 11.1
    
    def __new__(cls, *args, **kwargs):
        shape = kwargs.get('shape')
        if shape:
            n = shape[-1]
            i, k = args
        else:
            n, i, k = args
        
        n = _sympify(n)
        return MatrixExpr.__new__(cls, i, k, shape=(n, n))
    
    @property
    def multiplier(self):
        return self.args[-1]

    def _eval_transpose(self, *axis):
        if axis == self.default_axis:
            return self

    def _eval_inverse(self):
        return self.func(self.n, self.i, 1 / self.multiplier)

    @property
    def i(self):
        return self.args[-2]
    
    def _eval_determinant(self, **kwargs):
        return self.multiplier

    def _entry(self, i, j=None, **_):
        from sympy.concrete.expr_with_limits import Stack
#     1   0   0   0   0   0
#     0   1   0   0   0   0
#     0   0   k   0   0   0    <-----self.i    th row
#     0   0   0   1   0   0
#     0   0   0   0   1   0
#     0   0   0   0   0   1
#             ^       
#             |       
#            i col
        
        if j is None:
            return_reference = True
            j = self.generate_var(excludes=i.free_symbols, integer=True)
        else:
            return_reference = False
            
        piecewise = (1 + (self.multiplier - 1) * KroneckerDelta(i, self.i)) * KroneckerDelta(i, j)
        
        if return_reference:
            return Stack[j:self.n](piecewise)
        return piecewise

    @call_highest_priority('__rmatmul__')
    def __matmul__(self, rhs):
        if rhs.is_BlockMatrix:
            if rhs.axis == 1:
                if blocks := rhs.blocks:
                    rhs = rhs.func(blocks)
                else:
                    return MatrixExpr.__matmul__(self, rhs)  
            
            if rhs.axis == 0:
                other_i = rhs[self.i]
                if not other_i.is_Indexed:
                    args = []
                    if self.i != 0:
                        args.append(rhs[:self.i])
                    if other_i.is_BlockMatrix:
                        other_i = other_i.func(*[arg * self.multiplier for arg in other_i.args])
                    else:
                        other_i *= self.multiplier
                    args.append(other_i)
                    if self.i + 1 != self.shape[0]:
                        args.append(rhs[self.i + 1:])
                    
                    return rhs.func(*args, shape=rhs.shape)
            elif rhs.axis == 1:
                if blocks := rhs.blocks:
                    rhs = rhs.func(blocks)  
        elif rhs.is_DenseMatrix:
            d = rhs.shape[0]
            _args = [*rhs._args]
            for i in range(self.i * d, self.i * d + d):
                _args[i] *= self.multiplier
            return rhs.func(*_args, shape=rhs.shape)

        return MatrixExpr.__matmul__(self, rhs)

    @_sympifyit('lhs', NotImplemented)
    @call_highest_priority('__matmul__')
    def __rmatmul__(self, lhs):                
        if lhs.is_DenseMatrix:
            d = lhs.shape[0]
            _args = [*lhs._args]
            for i in range(self.i, self.i + d * d, d):
                _args[i] *= self.multiplier
            return lhs.func(*_args, shape=lhs.shape)
        if lhs.is_BlockMatrix:
            block = self.T @ lhs.T
            if block.is_BlockMatrix:
                return block.T
            
        return MatrixExpr.__rmatmul__(self, lhs)

    @property
    def dtype(self):
        return self.multiplier.dtype

    def _eval_is_extended_integer(self):
        return self.multiplier.is_extended_integer
    
    def _eval_is_finite(self):
        return self.multiplier.is_finite
     
    def _eval_is_singular(self):
        return self.multiplier.is_zero
    
    def _eval_is_extended_negative(self):
        if self.multiplier.is_extended_nonnegative:
            return False
        
    def _sympystr(self, p):
        n = self.shape[-1]
        i, j = self.args
        n = p._print(n)
        i = p._print(i)
        j = p._print(j)
        return f'MulMatrix({n}, {i}, {j})'

    def _lean(self, p):
        n = self.shape[-1]
        i, j = self.args
        n = p._print(n)
        i = p._print(i)
        j = p._print(j)
        return f'MulMatrix({n}, {i}, {j})'


class AddMatrix(ElementaryMatrix, MatrixExpr):
    '''
    multiply the ith row and add it to the jth row
    or multiply the ith column and add it to the jth column
    '''

    def __new__(cls, *args, **kwargs):
        shape = kwargs.get('shape')
        if shape:
            n = shape[-1]
        else:
            n, *args = args
        
        if len(args) == 2:
            args += (1,)
            
        n = _sympify(n)
        return MatrixExpr.__new__(cls, *args, shape=(n, n))
    
    @property
    def i(self):
        return self.args[0]
    
    @property
    def j(self):
        return self.args[1]

    def _eval_transpose(self, *axis):
        if axis == self.default_axis:
            return self.func(self.n, self.j, self.i, self.multiplier)

    def _eval_inverse(self):
        return self.func(self.n, self.i, self.j, -self.multiplier)

    def _entry(self, i, j=None, **_):
        from sympy.concrete.expr_with_limits import Stack
        from sympy.functions.elementary.piecewise import Piecewise
        from sympy.core.relational import Equal
        
#     1   0   0   0   0   0
#     0   1   0   0   0   0
#     0   0   1   0   0   0    <-----self.i    th row
#     0   0   0   1   0   0
#     0   0   k   0   1   0    <-----self.j th row
#     0   0   0   0   0   1
#             ^       ^
#             |       |
#            i col    j col
        
        if j is None:
            return_reference = True
            j = self.generate_var(excludes=i.free_symbols, integer=True)
        else:
            return_reference = False
            
        piecewise = Piecewise((KroneckerDelta(j, i), Equal(self.i, self.j)),
                              (Piecewise((self.multiplier, Equal(j, self.i)),
                                         (KroneckerDelta(j, self.j), True)),
                                         Equal(i, self.j)),
                              (KroneckerDelta(j, i), True))

        if return_reference:
            return Stack[j:self.n](piecewise)
        return piecewise

    def _eval_determinant(self, **kwargs):
        return S.One

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__rmatmul__')
    def __matmul__(self, other):
        if other.is_BlockMatrix:
            other_i = other[self.i]
            other_j = other[self.j]
            args = []
            if self.i < self.j or self.i > self.j:
                if self.j > 0:
                    args.append(other[:self.j])
                    
                args.append(other_i * self.multiplier + other_j)
                
                if self.j + 1 != self.shape[0]:
                    args.append(other[self.j + 1:])
                    
            else:
                return MatrixExpr.__matmul__(self, other)
            return other.func(*args, shape=other.shape).simplify()
        elif other.is_DenseMatrix:
            other_i = other[self.i]
            other_j = other[self.j]
            args = []
            if self.i < self.j or self.i > self.j: 
                for k in range(self.j):
                    args.append(other[k]._args)

                row = other_i * self.multiplier + other_j
                args.append(row._args)
                
                for k in range(self.j + 1, self.shape[0]):
                    args.append(other[k]._args)
            else:
                return MatrixExpr.__matmul__(self, other)
            return other.func(tuple(args)).simplify()  
            
        return MatrixExpr.__matmul__(self, other)

    @_sympifyit('lhs', NotImplemented)
    @call_highest_priority('__matmul__')
    def __rmatmul__(self, lhs):
        if lhs.is_DenseMatrix or lhs.is_BlockMatrix:
            if self.i < self.j or self.i > self.j:
#                 lhs @ self = (self.T @ lhs.T).T
                return (self.T @ lhs.T).T
            
        return MatrixExpr.__rmatmul__(self, lhs)

    @property
    def is_upper(self):
        return self.i >= self.j
    
    @property
    def is_lower(self):
        return self.i <= self.j

    @property
    def dtype(self):
        return self.multiplier.dtype

    @property
    def multiplier(self):
        return self.args[-1]
    
    def _eval_is_extended_integer(self):
        return self.multiplier.is_extended_integer
    
    def _eval_is_finite(self):
        return self.multiplier.is_finite
     
    def _eval_is_extended_negative(self):
        if self.multiplier.is_extended_nonnegative:
            return False
    
    def _sympystr(self, p):
        n = self.shape[-1]
        i, j, k = self.args
        n = p._print(n)
        i = p._print(i)
        j = p._print(j)
        k = p._print(k)
        return f'AddMatrix({n}, {i}, {j}, {k})'

    def _lean(self, p):
        n = self.shape[-1]
        i, j, k = self.args
        n = p._print(n)
        i = p._print(i)
        j = p._print(j)
        k = p._print(k)
        return f'AddMatrix({n}, {i}, {j}, {k})'


class ShiftMatrix(ElementaryMatrix, MatrixExpr):
    '''
    shift the ith row beyond the jth row
    or shift the jth column beyond the ith column
    '''
    
    def __new__(cls, *args, **kwargs):
        shape = kwargs.get('shape')
        if shape:
            n = shape[-1]
            i, j = args
        else:
            n, i, j = args
            
        n = _sympify(n)
        
        return MatrixExpr.__new__(cls, i, j, shape=(n, n))    

    @property
    def i(self):
        return self.args[-2]

    @property
    def j(self):
        return self.args[-1]
    
    def _eval_determinant(self, **kwargs):
        return (-1) ** (self.j - self.i)

    def _eval_transpose(self, *axis):
        if axis == self.default_axis:
            return ShiftMatrix(self.n, self.j, self.i)

    def _eval_inverse(self):
        return self.T

    def _entry(self, i, j=None, **_):
        from sympy.concrete.expr_with_limits import Stack
        from sympy.functions.elementary.piecewise import Piecewise
        from sympy.core.relational import Equal, Less
        from sympy.sets import Element, Range
        if j is None:
            return_reference = True
            j = self.generate_var(excludes=i.free_symbols, integer=True)
        else:
            return_reference = False
#     1   0   0   0   0   0
#     0   1   0   0   0   0
#     0   0   0   1   0   0    <-----self.i th row
#     0   0   0   0   1   0    delete i th row and insert after j th row
#     0   0   1   0   0   0    <-----self.j th row
#     0   0   0   0   0   1
#             ^       ^
#             |       |
#            i col    j col
#         
        piecewise_ij = Piecewise((KroneckerDelta(self.i, j), Equal(i, self.j)),
                                 (KroneckerDelta(i + 1, j), Element(i, Range(self.i, self.j))),
                                 (KroneckerDelta(i, j), True))
        
#     1   0   0   0   0   0
#     0   1   0   0   0   0
#     0   0   0   0   1   0    <-----self.j th row
#     0   0   1   0   0   0    delete i th row and insert before j th row
#     0   0   0   1   0   0    <-----self.i th row
#     0   0   0   0   0   1
#             ^       ^
#             |       |
#            j col    i col
        
        piecewise_ji = Piecewise((KroneckerDelta(i, self.j), Equal(j, self.i)),
                                 (KroneckerDelta(i, j + 1), Element(j, Range(self.j, self.i))),
                                 (KroneckerDelta(i, j), True))
        
        piecewise = Piecewise((KroneckerDelta(i, j), Equal(self.i, self.j)),
                              (piecewise_ij, Less(self.i, self.j)),
                              (piecewise_ji, True))

        if return_reference:
            return Stack[j:self.n](piecewise)
        return piecewise

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__rmatmul__')
    def __matmul__(self, other):
        if self.j == self.i:
            return other

        if other.is_BlockMatrix:
            if self.j > self.i:
                args = []
                if self.i > 0:
                    C = other[:self.i]
                    if C.is_BlockMatrix:
                        args += C.args
                    else:
                        args.append(C)
                
                A = other[self.i]
                B = other[self.i + 1:self.j + 1]
                
                if B.is_BlockMatrix:
                    args += B.args
                else:
                    args.append(B)
                args.append(A)

                if self.j + 1 < self.n:
                    C = other[self.j + 1:]
                    if C.is_BlockMatrix:
                        args += C.args
                    else:
                        args.append(C)

                return other.func(*args, shape=other.shape)

            elif self.j < self.i:
                ...

        return MatrixExpr.__matmul__(self, other)

    @property
    def is_upper(self):
        return self.i == self.j
    
    @property
    def is_lower(self):
        return self.i == self.j

    def _sympystr(self, p):
        n = self.shape[-1]
        i, j = self.args
        n = p._print(n)
        i = p._print(i)
        j = p._print(j)
        return f'ShiftMatrix({n}, {i}, {j})'

    def _lean(self, p):
        n = self.shape[-1]
        i, j = self.args
        n = p._print(n)
        i = p._print(i)
        j = p._print(j)
        return f'ShiftMatrix({n}, {i}, {j})'
