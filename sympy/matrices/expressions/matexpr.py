from functools import wraps, reduce
import collections

from sympy.core import S, Tuple, Integer, Basic, Expr, Eq, Mul, Add
from sympy.core.decorators import call_highest_priority
from sympy.core.compatibility import default_sort_key
from sympy.core.sympify import SympifyError, _sympify
from sympy.functions import conjugate
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.simplify import simplify
from sympy.core.cache import cacheit
from sympy.core.symbol import Symbol, DtypeMatrix


def _sympifyit(arg, retval=None):

    # This version of _sympifyit sympifies MutableMatrix objects
    def deco(func):

        @wraps(func)
        def __sympifyit_wrapper(a, b):
            try:
                b = _sympify(b)
                return func(a, b)
            except SympifyError:
                return retval

        return __sympifyit_wrapper

    return deco


class MatrixExpr(Expr):
    """Superclass for Matrix Expressions

    MatrixExprs represent abstract matrices, linear transformations represented
    within a particular basis.

    Examples
    ========

    >>> from sympy import MatrixSymbol
    >>> A = MatrixSymbol('A', 3, 3)
    >>> y = MatrixSymbol('y', 3, 1)
    >>> x = (A.T*A).I * A * y

    See Also
    ========

    MatrixSymbol, MatAdd, MatMul, Transpose, Inverse
    """

    # Should not be considered iterable by the
    # sympy.core.compatibility.iterable function. Subclass that actually are
    # iterable (i.e., explicit matrices) should set this to True.
    _iterable = False

    _op_priority = 11

    is_Matrix = True
    is_MatrixExpr = True
    is_Identity = None
    is_Inverse = False
    
    is_MatMul = False

#     is_commutative = False
    is_number = False
    is_symbol = False
    is_scalar = False
    
    def __new__(cls, *args, **kwargs):
        args = map(_sympify, args)
        return Basic.__new__(cls, *args, **kwargs)

    def __abs__(self):
        from sympy.functions.elementary.complexes import Abs
        return Abs(self, evaluate=False)

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__rmul__')
    def __mul__(self, other):
        return Mul(self, other)

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__rmatmul__')
    def __matmul__(self, other):
        return MatMul(self, other).doit()

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__mul__')
    def __rmul__(self, other):
        return Mul(other, self)

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__matmul__')
    def __rmatmul__(self, other):
        return MatMul(other, self).doit()

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__rpow__')
    def __pow__(self, other):
        if self.is_Identity:
            return self

        if other is S.Zero:
            return Ones(*self.shape)

        if other is S.One:
            return self

        from sympy.core.power import Pow
        return Pow(self, other, evaluate=False)

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__pow__')
    def __rpow__(self, other):
        from sympy.core.power import Pow
        return Pow(other, self, evaluate=False)

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__rdiv__')
    def __div__(self, other):
        return self * other ** S.NegativeOne

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__div__')
    def __rdiv__(self, other):  
        from sympy.core.power import Pow
        return Mul(other, Pow(self, S.NegativeOne))

    __truediv__ = __div__
    __rtruediv__ = __rdiv__

    @property
    def rows(self):
        if len(self.shape) == 1:
            return 1
        return self.shape[0]

    @property
    def cols(self):
        return self.shape[-1]

    def _eval_conjugate(self):
        if len(self.shape) < 2:
            return
        from sympy.matrices.expressions.adjoint import Adjoint
        from sympy.matrices.expressions.transpose import Transpose
        return Adjoint(Transpose(self))

    def as_real_imag(self, **_):
        from sympy import I
        conj = self._eval_conjugate()
        if conj is None:
            real = self
            im = S.Zero
        else:
            real = (self + conj) / 2
            im = (self - conj) / (2 * I)
        return real, im

    def _eval_inverse(self):
        from sympy.matrices.expressions.inverse import Inverse
        return Inverse(self)

    def _eval_transpose(self, *axis):
        ...

    def _eval_power(self, exp):
#         return MatPow(self, exp)
        ...

    def _eval_simplify(self, **kwargs):
        if self.is_Atom:
            return self
        else:
            return self.__class__(*[simplify(x, **kwargs) for x in self.args])

    def _eval_adjoint(self):
        from sympy.matrices.expressions.adjoint import Adjoint
        return Adjoint(self)

    def _eval_derivative(self, x):
        # x is a scalar:
        return Zeros(*self.shape)

    def _eval_derivative_array(self, x):
        if isinstance(x, MatrixExpr):
            return _matrix_derivative(self, x)
        else:
            return self._eval_derivative(x)

    def _eval_derivative_n_times(self, x, n):
        return Basic._eval_derivative_n_times(self, x, n)

    def _visit_eval_derivative_scalar(self, x):
        # `x` is a scalar:
        if x.has(self):
            return _matrix_derivative(x, self)
        else:
            return Zeros(*self.shape)

    def _visit_eval_derivative_array(self, x):
        if x.has(self):
            return _matrix_derivative(x, self)
        else:
            from sympy import Derivative
            return Derivative(x, self)

    def _accept_eval_derivative(self, s):
        return s._visit_eval_derivative_array(self)

    def as_coeff_Mul(self, rational=False):
        """Efficiently extract the coefficient of a product. """
        return S.One, self

    def conjugate(self):
        return conjugate(self)

    @property
    def I(self):
        return self.inverse()

    def valid_index(self, i, j):

        def is_valid(idx):
            return isinstance(idx, (int, Integer, Symbol, Expr))

        return (is_valid(i) and is_valid(j) and
                (self.rows is None or
                (0 <= i) != False and (i < self.rows) != False) and
                (0 <= j) != False and (j < self.cols) != False)

    def __getitem__(self, indices):
        if (indices := self.simplify_indices(indices)) is None:
            return self
        
        if isinstance(indices, Tuple):
            return self._entry(indices)
        
        if isinstance(indices, tuple):
            if len(indices) == 1:
                indices, = indices
            elif len(indices) == 2:
                i, j = indices
                if isinstance(i, Tuple) or isinstance(j, Tuple):
                    return self._entry(i, j)

                i, j = _sympify(i), _sympify(j)
                assert self.valid_index(i, j) != False
                return self._entry(i, j, expand=False)
            else:
                i, j, *rest = indices
                self = self._entry(i, j)
                if isinstance(i, Tuple):
                    if isinstance(j, Tuple):
                        return self._entry_multiple(slice(None), slice(None), *rest)
                    else:
                        return self[tuple((slice(None), *rest))]
                else: 
                    if isinstance(j, Tuple):
                        return self[tuple((slice(None), *rest))]
                    else:
                        return self[tuple(rest)]
                
        assert isinstance(indices, (int, Tuple)) or indices.is_Expr
        return self._entry(indices)

    def as_explicit(self):
        """
        Returns a dense Matrix with elements represented explicitly

        Returns an object of type ImmutableDenseMatrix.

        Examples
        ========

        >>> from sympy import Identity
        >>> I = Identity(3)
        >>> I
        I
        >>> I.as_explicit()
        Matrix([
        [1, 0, 0],
        [0, 1, 0],
        [0, 0, 1]])

        See Also
        ========
        as_mutable: returns mutable Matrix type

        """
        from sympy.matrices.immutable import ImmutableDenseMatrix
        return ImmutableDenseMatrix([[    self[i, j]
                            for j in range(self.cols)]
                            for i in range(self.rows)])

    def as_mutable(self):
        """
        Returns a dense, mutable matrix with elements represented explicitly

        Examples
        ========

        >>> from sympy import Identity
        >>> I = Identity(3)
        >>> I
        I
        >>> I.shape
        (3, 3)
        >>> I.as_mutable()
        Matrix([
        [1, 0, 0],
        [0, 1, 0],
        [0, 0, 1]])

        See Also
        ========
        as_explicit: returns ImmutableDenseMatrix
        """
        return self.as_explicit().as_mutable()

    def __array__(self):
        from numpy import empty
        a = empty(self.shape, dtype=object)
        for i in range(self.rows):
            for j in range(self.cols):
                a[i, j] = self[i, j]
        return a

    def equals(self, other):
        """
        Test elementwise equality between matrices, potentially of different
        types

        >>> from sympy import Identity, eye
        >>> Identity(3).equals(eye(3))
        True
        """
        return self.as_explicit().equals(other)

    def canonicalize(self):
        return self

    def as_coeff_mmul(self):
        return 1, MatMul(self)

    @staticmethod
    def from_index_summation(expr, first_index=None, last_index=None, dimensions=None):
        r"""
        Parse expression of matrices with explicitly summed indices into a
        matrix expression without indices, if possible.

        This transformation expressed in mathematical notation:

        `\sum_{j=0}^{N-1} A_{i,j} B_{j,k} \Longrightarrow \mathbf{A}\cdot \mathbf{B}`

        Optional parameter ``first_index``: specify which free index to use as
        the index starting the expression.

        Examples
        ========

        >>> from sympy import MatrixSymbol, MatrixExpr, Sum, Symbol
        >>> from sympy.abc import i, j, k, l, N
        >>> A = MatrixSymbol("A", N, N)
        >>> B = MatrixSymbol("B", N, N)
        >>> expr = Sum(A[i, j]*B[j, k], (j, 0, N-1))
        >>> MatrixExpr.from_index_summation(expr)
        A*B

        Transposition is detected:

        >>> expr = Sum(A[j, i]*B[j, k], (j, 0, N-1))
        >>> MatrixExpr.from_index_summation(expr)
        A.T*B

        Detect the trace:

        >>> expr = Sum(A[i, i], (i, 0, N-1))
        >>> MatrixExpr.from_index_summation(expr)
        Trace(A)

        More complicated expressions:

        >>> expr = Sum(A[i, j]*B[k, j]*A[l, k], (j, 0, N-1), (k, 0, N-1))
        >>> MatrixExpr.from_index_summation(expr)
        A*B.T*A.T
        """
        from sympy import Sum, Mul, Add, MatMul, transpose, trace
        from sympy.strategies.traverse import bottom_up

        def remove_matelement(expr, i1, i2):

            def repl_match(pos):

                def func(x):
                    if not isinstance(x, MatrixElement):
                        return False
                    if x.args[pos] != i1:
                        return False
                    if x.args[3 - pos] == 0:
                        if x.args[0].shape[2 - pos] == 1:
                            return True
                        else:
                            return False
                    return True

                return func

            expr = expr.replace(repl_match(1),
                lambda x: x.args[0])
            expr = expr.replace(repl_match(2),
                lambda x: transpose(x.args[0]))

            # Make sure that all Mul are transformed to MatMul and that they
            # are flattened:
            rule = bottom_up(lambda x: reduce(lambda a, b: a * b, x.args) if isinstance(x, (Mul, MatMul)) else x)
            return rule(expr)

        def recurse_expr(expr, index_ranges={}):
            if expr.is_Mul:
                nonmatargs = []
                pos_arg = []
                pos_ind = []
                dlinks = {}
                link_ind = []
                counter = 0
                args_ind = []
                for arg in expr.args:
                    retvals = recurse_expr(arg, index_ranges)
                    assert isinstance(retvals, list)
                    if isinstance(retvals, list):
                        for i in retvals:
                            args_ind.append(i)
                    else:
                        args_ind.append(retvals)
                for arg_symbol, arg_indices in args_ind:
                    if arg_indices is None:
                        nonmatargs.append(arg_symbol)
                        continue
                    if isinstance(arg_symbol, MatrixElement):
                        arg_symbol = arg_symbol.args[0]
                    pos_arg.append(arg_symbol)
                    pos_ind.append(arg_indices)
                    link_ind.append([None] * len(arg_indices))
                    for i, ind in enumerate(arg_indices):
                        if ind in dlinks:
                            other_i = dlinks[ind]
                            link_ind[counter][i] = other_i
                            link_ind[other_i[0]][other_i[1]] = (counter, i)
                        dlinks[ind] = (counter, i)
                    counter += 1
                counter2 = 0
                lines = {}
                while counter2 < len(link_ind):
                    for i, e in enumerate(link_ind):
                        if None in e:
                            line_start_index = (i, e.index(None))
                            break
                    cur_ind_pos = line_start_index
                    cur_line = []
                    index1 = pos_ind[cur_ind_pos[0]][cur_ind_pos[1]]
                    while True:
                        d, r = cur_ind_pos
                        if pos_arg[d] != 1:
                            if r % 2 == 1:
                                cur_line.append(transpose(pos_arg[d]))
                            else:
                                cur_line.append(pos_arg[d])
                        next_ind_pos = link_ind[d][1 - r]
                        counter2 += 1
                        # Mark as visited, there will be no `None` anymore:
                        link_ind[d] = (-1, -1)
                        if next_ind_pos is None:
                            index2 = pos_ind[d][1 - r]
                            lines[(index1, index2)] = cur_line
                            break
                        cur_ind_pos = next_ind_pos
                lines = {k: MatMul.fromiter(v) if len(v) != 1 else v[0] for k, v in lines.items()}
                return [(Mul.fromiter(nonmatargs), None)] + [
                    (MatrixElement(a, i, j), (i, j)) for (i, j), a in lines.items()
                ]
            elif expr.is_Add:
                res = [recurse_expr(i) for i in expr.args]
                d = collections.defaultdict(list)
                for res_addend in res:
                    scalar = 1
                    for elem, indices in res_addend:
                        if indices is None:
                            scalar = elem
                            continue
                        indices = tuple(sorted(indices, key=default_sort_key))
                        d[indices].append(scalar * remove_matelement(elem, *indices))
                        scalar = 1
                return [(MatrixElement(Add.fromiter(v), *k), k) for k, v in d.items()]
            elif isinstance(expr, KroneckerDelta):
                i1, i2 = expr.args
                if dimensions is not None:
                    identity = Identity(dimensions[0])
                else:
                    identity = S.One
                return [(MatrixElement(identity, i1, i2), (i1, i2))]
            elif isinstance(expr, MatrixElement):
                matrix_symbol, i1, i2 = expr.args
                if i1 in index_ranges:
                    r1, r2 = index_ranges[i1]
                    if r1 != 0 or matrix_symbol.shape[0] != r2 + 1:
                        raise ValueError("index range mismatch: {0} vs. (0, {1})".format(
                            (r1, r2), matrix_symbol.shape[0]))
                if i2 in index_ranges:
                    r1, r2 = index_ranges[i2]
                    if r1 != 0 or matrix_symbol.shape[1] != r2 + 1:
                        raise ValueError("index range mismatch: {0} vs. (0, {1})".format(
                            (r1, r2), matrix_symbol.shape[1]))
                if (i1 == i2) and (i1 in index_ranges):
                    return [(trace(matrix_symbol), None)]
                return [(MatrixElement(matrix_symbol, i1, i2), (i1, i2))]
            elif isinstance(expr, Sum):
                return recurse_expr(
                    expr.args[0],
                    index_ranges={i[0]: i[1:] for i in expr.args[1:]}
                )
            else:
                return [(expr, None)]

        retvals = recurse_expr(expr)
        factors, indices = zip(*retvals)
        retexpr = Mul.fromiter(factors)
        if len(indices) == 0 or list(set(indices)) == [None]:
            return retexpr
        if first_index is None:
            for i in indices:
                if i is not None:
                    ind0 = i
                    break
            return remove_matelement(retexpr, *ind0)
        else:
            return remove_matelement(retexpr, first_index, last_index)

    def applyfunc(self, func):
        from .applyfunc import ElementwiseApplyFunction
        return ElementwiseApplyFunction(func, self)

    def _eval_Eq(self, other):
        if isinstance(other, MatrixExpr) and not self - other:
            return True
        return Eq(self, other, evaluate=False)

    def _eval_is_random(self):
        return any(arg.is_random for arg in self.args)


def get_postprocessor(cls):

    def _postprocessor(expr):
        # To avoid circular imports, we can't have MatMul/MatAdd on the top level
        mat_class = {Mul: Mul, Add: Add}[cls]
        nonmatrices = []
        matrices = []
        for term in expr.args:
            if isinstance(term, MatrixExpr):
                matrices.append(term)
            else:
                nonmatrices.append(term)

        if not matrices:
            return cls._from_args(nonmatrices)

        if nonmatrices:
            if cls == Mul:
                return expr
                for i in range(len(matrices)):
                    if not matrices[i].is_MatrixExpr:
                        # If one of the matrices explicit, absorb the scalar into it
                        # (doit will combine all explicit matrices into one, so it
                        # doesn't matter which)
                        matrices[i] = matrices[i].__mul__(cls._from_args(nonmatrices))
                        nonmatrices = []
                        break

            else:
                # Maintain the ability to create Add(scalar, matrix) without
                # raising an exception. That way different algorithms can
                # replace matrix expressions with non-commutative symbols to
                # manipulate them like non-commutative scalars.
                return cls._from_args(nonmatrices + [mat_class(*matrices).doit(deep=False)])

        return mat_class(cls._from_args(nonmatrices), *matrices).doit(deep=False)

    return _postprocessor


Basic._constructor_postprocessor_mapping[MatrixExpr] = {
    "Mul": [get_postprocessor(Mul)],
    "Add": [get_postprocessor(Add)],
}


def _matrix_derivative(expr, x):
    from sympy import Derivative
    lines = expr._eval_derivative_matrix_lines(x)

    parts = [i.build() for i in lines]

    from sympy.codegen.array_utils import recognize_matrix_expression

    parts = [[recognize_matrix_expression(j).doit() for j in i] for i in parts]

    def _get_shape(elem):
        if isinstance(elem, MatrixExpr):
            return elem.shape
        return (1, 1)

    def get_rank(parts):
        return sum([j not in (1, None) for i in parts for j in _get_shape(i)])

    ranks = [get_rank(i) for i in parts]
    rank = ranks[0]

    def contract_one_dims(parts):
        if len(parts) == 1:
            return parts[0]
        else:
            p1, p2 = parts[:2]
            if p2.is_Matrix:
                p2 = p2.T
            pbase = p1 * p2
            if len(parts) == 2:
                return pbase
            else:  # len(parts) > 2
                if pbase.is_Matrix:
                    raise ValueError("")
                return pbase * Mul.fromiter(parts[2:])

    if rank <= 2:
        return Add.fromiter([contract_one_dims(i) for i in parts])

    return Derivative(expr, x)


class MatrixElement(Expr):
    parent = property(lambda self: self.args[0])
    i = property(lambda self: self.args[1])
    j = property(lambda self: self.args[2])
    _diff_wrt = True
    is_symbol = True
    is_commutative = True

    def __new__(cls, name, n, m=None):
        if m is None:
            n = _sympify(n)

            if isinstance(name, str):
                name = Symbol(name)
            name = _sympify(name)
            obj = Expr.__new__(cls, name, n)
        else:
            n, m = map(_sympify, (n, m))
            from sympy import MatrixBase
            if isinstance(name, (MatrixBase,)):
                if n.is_Integer and m.is_Integer:
                    return name[n, m]
            if isinstance(name, str):
                name = Symbol(name)
            name = _sympify(name)
            obj = Expr.__new__(cls, name, n, m)
        return obj

    def doit(self, **kwargs):
        deep = kwargs.get('deep', True)
        if deep:
            args = [arg.doit(**kwargs) for arg in self.args]
        else:
            args = self.args
        return args[0][args[1], args[2]]

    @property
    def indices(self):
        return self.args[1:]

    def _eval_derivative(self, v):
        from sympy import Sum, symbols, Dummy

        if not isinstance(v, MatrixElement):
            from sympy import MatrixBase
            if isinstance(self.parent, MatrixBase):
                return self.parent.diff(v)[self.i, self.j]
            return S.Zero

        M = self.args[0]

        if M == v.args[0]:
            return KroneckerDelta(self.args[1], v.args[1]) * KroneckerDelta(self.args[2], v.args[2])

        if isinstance(M, Inverse):
            i, j = self.args[1:]
            i1, i2 = symbols("z1, z2", cls=Dummy)
            Y = M.args[0]
            r1, r2 = Y.shape
            return -Sum(M[i, i1] * Y[i1, i2].diff(v) * M[i2, j], (i1, 0, r1 - 1), (i2, 0, r2 - 1))

        if self.has(v.args[0]):
            return None

        return S.Zero


class MatrixSymbol(MatrixExpr):
    """Symbolic representation of a Matrix object

    Creates a SymPy Symbol to represent a Matrix. This matrix has a shape and
    can be included in Matrix Expressions

    Examples
    ========

    >>> from sympy import MatrixSymbol, Identity
    >>> A = MatrixSymbol('A', 3, 4) # A 3 by 4 Matrix
    >>> B = MatrixSymbol('B', 4, 3) # A 4 by 3 Matrix
    >>> A.shape
    (3, 4)
    >>> 2*A*B + Identity(3)
    I + 2*A*B
    """
#     is_commutative = False
    is_symbol = True
    _diff_wrt = True

    def __new__(cls, name, n, m):
        n, m = _sympify(n), _sympify(m)
        if isinstance(name, str):
            name = Symbol(name)
        obj = Basic.__new__(cls, name, n, m)
        return obj

    def _hashable_content(self):
        return (self.name, self.shape)

    @cacheit
    def _eval_shape(self):
        return self.args[1:3]

    @property
    def name(self):
        return self.args[0].name

    def _eval_subs(self, old, new, **hints):
        # only do substitutions in shape
        shape = Tuple(*self.shape)._subs(old, new, **hints)
        return MatrixSymbol(self.name, *shape)

    def __call__(self, *args):
        raise TypeError("%s object is not callable" % self.__class__)

    def _entry(self, i, j, **kwargs):
        return MatrixElement(self, i, j)

    def _eval_free_symbols(self):
        return {self}

    def doit(self, **hints):
        if hints.get('deep', True):
            return type(self)(self.name, self.args[1].doit(**hints),
                    self.args[2].doit(**hints))
        else:
            return self

    def _eval_simplify(self, **kwargs):
        return self

    def _eval_derivative_matrix_lines(self, x):
        if self != x:
            first = Zeros(x.shape[0], self.shape[0]) if self.shape[0] != 1 else S.Zero
            second = Zeros(x.shape[1], self.shape[1]) if self.shape[1] != 1 else S.Zero
            return [_LeftRightArgs(
                [first, second],
            )]
        else:
            first = Identity(self.shape[0]) if self.shape[0] != 1 else S.One
            second = Identity(self.shape[1]) if self.shape[1] != 1 else S.One
            return [_LeftRightArgs(
                [first, second],
            )]


class ConstantMatrix:
    
    def _eval_subs(self, old, new, **hints):
        
        hit = False
        shape = [*self.shape]
        for i, size in enumerate(self.shape):
            size = size._subs(old, new, **hints)
            if size != self.shape[i]:
                hit = True

            shape[i] = size
        
        args = [*self.args]
        for i, arg in enumerate(args):
            _arg = arg._subs(old, new, **hints)
            if _arg != arg:
                hit = True
                args[i] = _arg

        if hit:
            return self.func(*args, shape=tuple(shape))
        
        return self

    @property
    def dtype(self):
        from sympy.core.symbol import dtype
        return dtype.integer
    
    @cacheit
    def _has(self, pattern):
        return any(isinstance(size, Basic) and size._has(pattern) for size in self.shape) or MatrixExpr._has(self, pattern)
    
    @property
    def kwargs(self):
        return dict(shape=self.shape)
    
    def _hashable_content(self):
        return (*self.shape, *self._args)
    

class Identity(ConstantMatrix, MatrixExpr):
    """The Matrix Identity I - multiplicative identity

    Examples
    ========

    >>> from sympy.matrices import Identity, MatrixSymbol
    >>> A = MatrixSymbol('A', 3, 5)
    >>> I = Identity(3)
    >>> I*A
    A
    """
    is_upper = True
    is_lower = True
    is_singular = False
    is_finite = True

    def __new__(cls, *args, **kwargs):
        if args:
            n, = args
        else:
            n, S[n] = kwargs['shape']
            
        if n == 1:
            return S.One
         
        return super(Identity, cls).__new__(cls, shape=(n, n))

    def _latex(self, p):
        return r"\mathbb{I}" if p._settings['mat_symbol_style'] == 'plain' else r"\mathbf{I}"

    def _sympystr(self, p):
        n = self.shape[-1]
        n = p._print(n)
        return f"Identity({n})"

    def _lean(self, p):
        n = self.shape[-1]
        n = p._print(n)
        return f"eye {n}"
    
    @property
    def n(self):
        return self.shape[-1]

    @property
    def rows(self):
        return self.shape[-1]

    @property
    def cols(self):
        return self.shape[-2]
    
    @property
    def is_square(self):
        return True

    def _eval_transpose(self, *axis):
        if axis == self.default_axis:
            return self

    def _eval_trace(self):
        return self.rows

    def _eval_inverse(self):
        return self

    def conjugate(self):
        return self

    def _entry(self, i, j=None, **_):
        from sympy import BlockMatrix, Zeros, Stack
        if j is None:
            if isinstance(i, Tuple):
                start, stop, step = i.slice_args
                assert step == 1 or step is None
                n = self.shape[-1]
                
                size = stop - start
                if start == 0:
                    if size == n:
                        return self

                    assert 0 < size < n
                    return BlockMatrix[1](self.func(size), Zeros(size, n - size), shape=(size, n))
                elif stop == n:
                    assert start > 0
                    return BlockMatrix[1](Zeros(size, start), self.func(size), shape=(size, n))
                else:
                    raise Exception("unimplemented")
            else:
                j = self.generate_var(excludes=set() if isinstance(i, int) else i.free_symbols, integer=True)
                return Stack[j:self.n](KroneckerDelta(i, j))

        elif isinstance(i, Tuple):
            start, stop, step = i.slice_args
            if start == 0 and stop == self.shape[0] and step == 1:
                if isinstance(j, Tuple):
                    start, stop, step = j.slice_args
                    assert step == 1
                    n = self.shape[-1]
                    size = stop - start
                    
                    if start == 0:
                        if size == n:
                            return self
    
                        assert 0 < size < n
                        return BlockMatrix(self.func(size), Zeros(n - size, size), shape=(n, size))
                    elif stop == n:
                        assert start > 0
                        return BlockMatrix(Zeros(start, size), self.func(size), shape=(n, size))
                    else:
                        raise Exception("unimplemented")
                else:
                    i = self.generate_var(excludes=j.free_symbols, integer=True)
                    return Stack[i:self.n](KroneckerDelta(i, j))
            else:
                raise Exception("unimplemented")
        else:
            eq = Eq(i, j)
            if eq is S.true:
                return S.One
            elif eq is S.false:
                return S.Zero
            return KroneckerDelta(i, j)

    def _eval_determinant(self, **kwargs):
        return S.One

    def _eval_is_extended_integer(self):
        return True

    def _eval_is_extended_positive(self):
        ...
        
    def _eval_is_extended_negative(self):
        return False
    
    def doit(self, **hints):
        if hints.get('deep'):
            shape = self.shape
            if len(shape) == 2:
                n = shape[-1]
                if isinstance(n, int) or n.is_Number:
                    n = int(n)
                    m = [[S.Zero] * n for i in range(n)]
                    for i in range(n):
                        m[i][i] = S.One
                    from sympy import Matrix
                    return Matrix(tuple(tuple(v) for v in m))
            
        return self
    
    def __rmul__(self, other): 
        if isinstance(other, Basic) and len(other.shape) >= len(self.shape):
            return other
        return Mul(other, self)
    
    def _eval_conjugate(self):
        return self


def simplify_shape(shape):
    while shape:
        if shape[0] == 1:
            shape = shape[1:]
        elif shape[-1] == 1:
            shape = shape[:-1]
        else:
            break
            
    return shape
    
    
class Zeros(ConstantMatrix, MatrixExpr):
    """The Matrix Zero 0 - additive identity

    Examples
    ========

    >>> from sympy import MatrixSymbol, Zeros
    >>> A = MatrixSymbol('A', 3, 5)
    >>> Z = Zeros(3, 5)
    >>> A + Z
    A
    >>> Z*A.T
    0
    """
    is_zero = True
    
    def __new__(cls, *shape, **kwargs):
        shape = kwargs.get('shape', shape)
        shape = simplify_shape(shape)
        if not shape:
            return S.Zero
        return super(Zeros, cls).__new__(cls, shape=shape)

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__rpow__')
    def __pow__(self, other):
        if other > 0:
            return self
        if other == 0:
            return Ones(*self.shape)
        if other < 0:
            raise ValueError("Matrix det == 0; not invertible.")

        from sympy import Pow
        return Pow(self, other, evaluate=False)

    def _eval_transpose(self, *axis):
        if axis == self.default_axis:
            if len(self.shape) <= 1:
                return self
            *shape, rows, cols = self.shape
            return Zeros(cols, rows, *shape)

    def _eval_trace(self):
        return S.Zero

    def _eval_determinant(self, **kwargs):
        return S.Zero

    def conjugate(self):
        return self

    @staticmethod
    def static_entry(self, i, j):
        from sympy.functions.elementary.integers import Ceil
        if j is None:
            if isinstance(i, Tuple):
                start, stop, step = i.slice_args
                size = stop - start
                return self.func(Ceil(size / step), *self.shape[1:])
            
            return self.func(*self.shape[1:])
            
        elif isinstance(i, Tuple):
            start, stop, step = i.slice_args
            if start == 0 and stop == self.shape[0] and step == 1:
                if isinstance(j, Tuple):
                    start, stop, step = j.slice_args
                    size = stop - start
                    return self.func(self.shape[0], Ceil(size / step), *self.shape[2:])
                else:
                    return self.func(self.shape[0])
            raise Exception('unimplemented slice object %s' % i)
        
        return self.func(*self.shape[2:])
        
    def _entry(self, i, j=None, **kwargs):
        return Zeros.static_entry(self, i, j)

    def __bool__(self):
        return False

    def _latex(self, p):
        return r'\mathbf{0}_{%s}' % ','.join(map(p._print, self.shape))
#         return r"\mathbb{0}" if p._settings['mat_symbol_style'] == 'plain' else r"\mathbf{0}"

    def _sympystr(self, p):
        return "Zeros(%s)" % ", ".join(p._print(s) for s in self.shape)

    def _lean(self, p):
        return "Zeros [%s]" % ", ".join(p._print(s) for s in self.shape)

    def __rmul__(self, other): 
        if isinstance(other, Basic) and len(other.shape) > len(self.shape):
            return self.func(*other.shape)
        return self

    def __mul__(self, lhs):
        if isinstance(lhs, Basic) and len(lhs.shape) > len(self.shape):
            return self.func(*lhs.shape)
        return self
    
    def __add__(self, other):
        if len(other.shape) < len(self.shape):
            return Ones(*self.shape) * other
        return other

    def __radd__(self, other):
        if len(other.shape) < len(self.shape):
            return Ones(*self.shape) * other
        return other
    
    def doit(self, **hints):
        return self
    
    @staticmethod
    def simplify_Lamda(self, squeeze=False):
        if squeeze:
            return S.Zero
        
        shape = []
        for v, *ab in self.limits:
            if len(ab) == 2:
                a, b = ab
                size = b - a
            elif not ab:
                from sympy.sets.fancysets import Range
                a, b = v.domain.of(Range)
                size = b - a
            shape.append(size)
        shape.reverse()
        return Zeros(*shape, *self.expr.shape)
    
    def _eval_exp(self):
        return Ones(*self.shape)
    
    def of(self, cls):
        if cls.is_Zero or cls.is_Zeros:
            return ()

    def is_consistently_of(self, struct):
        return struct.is_Zeros or struct.is_Zero

    def _eval_conjugate(self):
        return self

    def _eval_Norm(self):
        return self.func(*self.shape[:-1])

    def python_definition(self, free_symbols, random_symbols):
        return DtypeMatrix.python_definition(self, free_symbols, random_symbols)


class GenericZeroMatrix(Zeros):
    """
    A zero matrix without a specified shape

    This exists primarily so MatAdd() with no arguments can return something
    meaningful.
    """

    def __new__(cls):
        # super(Zeros, cls) instead of super(GenericZeroMatrix, cls)
        # because Zeros.__new__ doesn't have the same signature
        return super(Zeros, cls).__new__(cls)

    @property
    def rows(self):
        raise TypeError("GenericZeroMatrix does not have a specified shape")

    @property
    def cols(self):
        raise TypeError("GenericZeroMatrix does not have a specified shape")

    def _eval_shape(self):
        raise TypeError("GenericZeroMatrix does not have a specified shape")

    # Avoid Matrix.__eq__ which might call .shape
    def __eq__(self, other):
        return isinstance(other, GenericZeroMatrix)

    def __ne__(self, other):
        return not (self == other)

    def __hash__(self):
        return super(GenericZeroMatrix, self).__hash__()


class Ones(ConstantMatrix, MatrixExpr):
    """
    Matrix whose all entries are ones.
    """
    is_integer = True
    is_extended_positive = True
    is_extended_negative = False
    is_finite = True
    
    def __new__(cls, *shape, **kwargs):
        if len(shape) == 1 and isinstance(shape[0], tuple):
            shape, = shape
        else:
            shape = kwargs.get('shape', shape)
        shape = simplify_shape(shape)
        if not shape:
            return S.One
        return super(Ones, cls).__new__(cls, shape=shape)

    def as_explicit(self):
        from sympy import ImmutableDenseMatrix
        return ImmutableDenseMatrix.ones(*self.shape)

    def _eval_transpose(self, *axis):
        if axis == self.default_axis:
            if len(self.shape) <= 1:
                return self
            *shape, rows, cols = self.shape
            return Ones(cols, rows, *shape)

    def _eval_trace(self):
        return S.One * self.rows

    def _eval_determinant(self, **kwargs):
        condition = Eq(self.shape[0], 1) & Eq(self.shape[1], 1)
        if condition == True:
            return S.One
        elif condition == False:
            return S.Zero
        
    def conjugate(self):
        return self

    def _entry(self, i, j=None, **_):
        return Zeros.static_entry(self, i, j)

    def _latex(self, p):
        return r'\mathbf{1}_{%s}' % ','.join(map(p._print, self.shape))
#         return r"\mathbb{1}" if p._settings['mat_symbol_style'] == 'plain' else r"\mathbf{1}"

    def _sympystr(self, p):
        return "Ones(%s)" % ", ".join(p._print(s) for s in self.shape)

    def _lean(self, p):
        return "Ones [%s]" % ", ".join(p._print(s) for s in self.shape)

    def __mul__(self, rhs):
        if len(rhs.shape) >= len(self.shape):
            return rhs
        return MatrixExpr.__mul__(self, rhs)
    
    def __rmul__(self, lhs):
        if len(lhs.shape) >= len(self.shape):
            return lhs
        return MatrixExpr.__mul__(self, lhs)
    
    def _eval_power(self, exp):
        return self
    
    def doit(self, **hints):
        return self

    def _eval_is_extended_integer(self):
        return True

    @staticmethod
    def simplify_Lamda(self, squeeze=False):
        if squeeze:
            return S.One
        
        shape = []
        for v, *ab in self.limits:
            if len(ab) == 2:
                a, b = ab
                size = b - a
            elif not ab:
                from sympy.sets.fancysets import Range
                a, b = v.domain.of(Range)
                size = b - a
            shape.append(size)
        shape.reverse()
        return Ones(*shape, *self.expr.shape)
    
    @staticmethod
    def expand_dims(self, shape, pivot):
        consistent_shape = shape[:-pivot] 
        extra_shape = shape[-pivot:]
        consistent_shape_len = len(consistent_shape)
#                   transpose matrix from (*consistent_shape, *extra_shape) to (*extra_shape, *consistent_shape)
#                   (3, 4, 5, 6) => (5, 6, 3, 4)
        axes = []
        for j in range(len(extra_shape)):
            for i in range(consistent_shape_len):
                axes.append(consistent_shape_len + j - i)

        from sympy import Transpose
        return Transpose[tuple(axes)](self * Ones(*consistent_shape, *extra_shape))

    def is_consistently_of(self, struct):
        return struct.is_Ones

    def _eval_conjugate(self):
        return self

    def _eval_Norm(self):
        return self.func(*self.shape[:-1]) * self.shape[-1]

    def python_definition(self, free_symbols, random_symbols):
        return DtypeMatrix.python_definition(self, free_symbols, random_symbols)


def matrix_symbols(expr):
    return [sym for sym in expr.free_symbols if sym.is_Matrix]


class _LeftRightArgs(object):
    r"""
    Helper class to compute matrix derivatives.

    The logic: when an expression is derived by a matrix `X_{mn}`, two lines of
    matrix multiplications are created: the one contracted to `m` (first line),
    and the one contracted to `n` (second line).

    Transposition flips the side by which new matrices are connected to the
    lines.

    The trace connects the end of the two lines.
    """

    def __init__(self, lines, higher=S.One):
        self._lines = [i for i in lines]
        self._first_pointer_parent = self._lines
        self._first_pointer_index = 0
        self._first_line_index = 0
        self._second_pointer_parent = self._lines
        self._second_pointer_index = 1
        self._second_line_index = 1
        self.higher = higher

    @property
    def first_pointer(self):
        return self._first_pointer_parent[self._first_pointer_index]

    @first_pointer.setter
    def first_pointer(self, value):
        self._first_pointer_parent[self._first_pointer_index] = value

    @property
    def second_pointer(self):
        return self._second_pointer_parent[self._second_pointer_index]

    @second_pointer.setter
    def second_pointer(self, value):
        self._second_pointer_parent[self._second_pointer_index] = value

    def __repr__(self):
        try:
            built = [self._build(i) for i in self._lines]
        except Exception:
            built = self._lines
        return "_LeftRightArgs(lines=%s, higher=%s)" % (
            built,
            self.higher,
        )

    def transpose(self):
        self._first_pointer_parent, self._second_pointer_parent = self._second_pointer_parent, self._first_pointer_parent
        self._first_pointer_index, self._second_pointer_index = self._second_pointer_index, self._first_pointer_index
        self._first_line_index, self._second_line_index = self._second_line_index, self._first_line_index
        return self

    @staticmethod
    def _build(expr):
        from sympy.core.expr import ExprBuilder
        if isinstance(expr, ExprBuilder):
            return expr.build()
        if isinstance(expr, list):
            if len(expr) == 1:
                return expr[0]
            else:
                return expr[0](*[_LeftRightArgs._build(i) for i in expr[1]])
        else:
            return expr

    def build(self):
        data = [self._build(i) for i in self._lines]
        if self.higher != 1:
            data += [self._build(self.higher)]
        data = [i.doit() for i in data]
        return data

    def matrix_form(self):
        if self.first != 1 and self.higher != 1:
            raise ValueError("higher dimensional array cannot be represented")

        def _get_shape(elem):
            if isinstance(elem, MatrixExpr):
                return elem.shape
            return (None, None)

        if _get_shape(self.first)[1] != _get_shape(self.second)[1]:
            # Remove one-dimensional identity matrices:
            # (this is needed by `a.diff(a)` where `a` is a vector)
            if _get_shape(self.second) == (1, 1):
                return self.first * self.second[0, 0]
            if _get_shape(self.first) == (1, 1):
                return self.first[1, 1] * self.second.T
            raise ValueError("incompatible shapes")
        if self.first != 1:
            return self.first * self.second.T
        else:
            return self.higher

    def rank(self):
        """
        Number of dimensions different from trivial (warning: not related to
        matrix rank).
        """
        rank = 0
        if self.first != 1:
            rank += sum([i != 1 for i in self.first.shape])
        if self.second != 1:
            rank += sum([i != 1 for i in self.second.shape])
        if self.higher != 1:
            rank += 2
        return rank

    def _multiply_pointer(self, pointer, other):
        from sympy.core.expr import ExprBuilder
        from sympy.codegen.array_utils import CodegenArrayContraction, CodegenArrayTensorProduct

        subexpr = ExprBuilder(
            CodegenArrayContraction,
            [
                ExprBuilder(
                    CodegenArrayTensorProduct,
                    [
                        pointer,
                        other
                    ]
                ),
                (1, 2)
            ],
            validator=CodegenArrayContraction._validate
        )

        return subexpr

    def append_first(self, other):
        self.first_pointer *= other

    def append_second(self, other):
        self.second_pointer *= other

    def __hash__(self):
        return hash((self.first, self.second))

    def __eq__(self, other):
        if not isinstance(other, _LeftRightArgs):
            return False
        return (self.first == other.first) and (self.second == other.second)


def _make_matrix(x):
    from sympy import ImmutableDenseMatrix
    if isinstance(x, MatrixExpr):
        return x
    return ImmutableDenseMatrix([[x]])

    
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


from .matmul import MatMul
from .matpow import MatPow
from .inverse import Inverse
