from sympy import Number
from sympy.core import Mul, Basic, sympify

from sympy.strategies import (rm_id, unpack, typed, flatten, exhaust,
        do_one, new)
from sympy.matrices.expressions.matexpr import MatrixExpr, Identity, Zeros
from sympy.matrices.common import ShapeError
from sympy.matrices.expressions.blockmatrix import BlockMatrix
from sympy.matrices.expressions.matpow import MatPow
from sympy.matrices.matrices import MatrixBase
from sympy.core.logic import fuzzy_and
from sympy.core.cache import cacheit
from sympy.core.containers import Tuple


class MatMul(MatrixExpr): 
    """
    A product of matrix expressions

    Examples
    ========

    >>> m = 2
    >>> n = 2
    >>> a = Symbol(real=True, shape=(m, n))
    >>> m1 = Matrix([[a[i, j] for j in range(n)] for i in range(m)])
    >>> m1
    >>> l = 2
    >>> b = Symbol(real=True, shape=(n, l))
    >>> m2 = Matrix([[b[i, j] for j in range(l)] for i in range(n)])
    >>> m2
    >>> discrete.matmul.to.matrix.apply(MatMul(m1, m2))    
    """

    precedence = 45

    def __new__(cls, *args, **kwargs):
#         check = kwargs.get('check', True)
        check = kwargs.get('check', False)

        assert args

        if len(args) == 1:
            return args[0]

        # This must be removed aggressively in the constructor
        args = list(map(sympify, args))
        
        if any(arg.is_MatMul for arg in args):

            def generator():
                size = len(args)
                for i, arg in enumerate(args):
                    if arg.is_MatMul:
                        if i + 1 < size and len(arg.args[-1].shape) == 1:
#                             len(args[i + 1].shape) == 1
                            for t in reversed(arg.args):
                                yield t.T

                        elif i and len(arg.args[0].shape) == 1:
#                             if len(args[i - 1].shape) == 1:
                            for t in reversed(arg.args):
                                yield t.T

                        else:
                            yield from arg.args
                    else:
                        yield arg
                        
            args = [*generator()]
            
        coeffs = []
        matrices = []

        def append(mat): 
            if matrices:
                last = matrices[-1]
                if last.is_MatPow:
                    if mat.is_MatPow:
                        if last.base == mat.base:
                            matrices[-1] = last.func(last.base, last.exp + mat.exp)
                            return
                    elif last.base == mat: 
                        matrices[-1] = last.func(last.base, last.exp + 1)
                        return

                elif last == mat:
                    if mat.is_square:
                        if mat._eval_inverse() == last:
                            matrices.pop()
                        else:
                            matrices[-1] = MatPow(last, 2)
                        return
                    
                elif len(last.shape) == 1 and len(mat.shape) > 1:
                    if len(matrices) > 1:
                        second_last = matrices[-2]
                        if len(second_last.shape) > 1:
                            matrices[-1], matrices[-2] = second_last.T, last
                    
            if mat.is_Zeros:
                from sympy import S
                coeffs.append(S.Zero)
            
            if mat.is_MatMul:
                args = mat.args
                if matrices:
                    if last.is_square and last.inverse() == args[0]:
                        matrices.pop()
                        args = args[1:]
                matrices.extend(args) 
            else:
                matrices.append(mat)
                
        for arg in args:
            if arg.is_Mul:
                coeff = []
                matrix = []
                for t in arg.args:
                    if t.shape:
                        matrix.append(t)
                    else:
                        coeff.append(t)
                if coeff:
                    coeffs.append(Mul(*coeff))
                    append(Mul(*matrix))
                else:
                    append(arg)
            else:
                if arg.shape:
                    append(arg)
                else:
                    coeffs.append(arg)
                
        if not matrices:
            coeffs = Mul(*coeffs)
            if args[0].shape:
                return coeffs * Identity(args[0].shape[-1])
            return coeffs

        matrices = [*filter(lambda X: not X.is_Identity, matrices)]
                        
        if len(matrices) == 1:
            mat = matrices.pop()
        elif not matrices:
            return Identity(args[0].shape[-1])
        
        else:
            mat = Basic.__new__(cls, *matrices)
            factor, matrices = mat.as_coeff_matrices()
            if check:
                validate(*matrices)
            if not matrices:
                mat = factor
        
        if coeffs: 
            mat = Mul(*coeffs) * mat
                        
        return mat

    def argmax_shape(self):
        import numpy as np
        return np.argmax([len(arg.shape) for arg in self.args])

    @staticmethod
    def matmul_shape(lhs_shape, rhs_shape):
        len_lhs_shape = len(lhs_shape)
        len_rhs_shape = len(rhs_shape)
        
        if len_lhs_shape > len_rhs_shape:
            if len_rhs_shape == 2:
                *batch_size, n, k = lhs_shape
                _k, m = rhs_shape
                assert k == _k
                return (*batch_size, n, m)               
            else:
                *batch_size, n, k = lhs_shape
                * _batch_size, _k = rhs_shape
                assert k == _k
                if len(batch_size) == len(_batch_size):
                    assert batch_size == _batch_size
                else:
                    assert batch_size[:-len(_batch_size)] == _batch_size
                return (*batch_size, n)                
        elif len_lhs_shape < len_rhs_shape:
            *_batch_size, k = lhs_shape
            * batch_size, _k, n = rhs_shape
            assert k == _k
            if len(batch_size) == len(_batch_size):
                assert batch_size == _batch_size, "%s, %s, batch_size mismatch!" % (lhs_shape, rhs_shape)
            else:
                assert batch_size[:-len(_batch_size)] == _batch_size
            return (*batch_size, n)                
        else:
            if len_lhs_shape == 1:
                assert lhs_shape == rhs_shape
                return ()
            * batch_size, n, k = lhs_shape
            * _batch_size, _k, m = rhs_shape
            assert k == _k, f"{lhs_shape}, {rhs_shape} are not compatible in matrix multiplication"
            assert batch_size == _batch_size
            return (*batch_size, n, m)
            
    @cacheit
    def _eval_shape(self):
        shape = self.args[0].shape
        for i in range(1, len(self.args)):
            shape = self.matmul_shape(shape, self.args[i].shape)
        return shape

    def _entry_multiple(self, i, j=None, *rest):
        len_shape = self.max_len_shape()
        args = [*self.args]
        for t, arg in enumerate(args):
            if len(arg.shape) == len_shape:
                args[t] = arg[i]
        
        if isinstance(i, slice):
            if len_shape > 3:
                for t, arg in enumerate(args):
                    if len(arg.shape) == len_shape:
                        args[t] = arg[:, j]
                    elif len(arg.shape) == len_shape - 1:
                        args[t] = arg[j]

                raise Exception("unresolved case")
            else:
                if len(args[0].shape) == len_shape:
                    args[0] = args[0][:, j]
                else:
                    for t, arg in enumerate(args):
                        if len(arg.shape) == len_shape:
                            args[t] = arg[:, j]
                            break
                        
                args[-1] = args[-1][tuple(*[slice(None)] * (len(args[-1].shape) - 1), *rest)]
            
            return MatMul(*args)
        else:
            return MatMul(*args)[tuple(j, *rest)]
        
    def _entry(self, i, j=None, expand=True, **kwargs):
        if j is None:
            if len(self.args[0].shape) == 1:
                return self.args[0] @ self.func(*self.args[1:])[:, i]
            rhs = self.func(*self.args[1:])
            if len(rhs.shape) > 2:
                rhs = rhs[i]
            return self.args[0][i] @ rhs
        
        if len(self.shape) > 2:
            len_shape = self.max_len_shape()
            args = [*self.args]
            for t, arg in enumerate(args):
                if len(arg.shape) == len_shape:
                    args[t] = arg[i]
            
            if isinstance(i, Tuple):
                if len_shape > 3:
                    for t, arg in enumerate(args):
                        if len(arg.shape) == len_shape:
                            args[t] = arg[:, j]
                        elif len(arg.shape) == len_shape - 1:
                            args[t] = arg[j]
                else:
                    if len(args[0].shape) == len_shape:
                        args[0] = args[0][:, j]
                    else:
                        for t, arg in enumerate(args):
                            if len(arg.shape) == len_shape:
                                args[t] = arg[:, j]
                                break
                            
                return MatMul(*args)
            else:
                return MatMul(*args)[j]
        
        if isinstance(i, Tuple):
            start, stop, step = i.slice_args
            if start == 0:
                if stop == self.shape[0] and step == 1:
                    return self.func(*self.args[:-1]) @ self.args[-1][:, j]
                
            return
        
        if isinstance(j, Tuple):
            start, stop, step = j.slice_args
            if start == 0:
                if stop == self.shape[1] and step == 1:
                    return self.func(*self.args[:-1]) @ self.args[-1][:, j]
                
            return self.func(*self.args[:-1])[i] @ self.args[-1][:, start:stop]
        
        if expand: 
            from sympy import Dummy, Sum, ImmutableMatrix, Integer
    
            coeff, matrices = self.as_coeff_matrices()
    
            if len(matrices) == 1:  # situation like 2*X, matmul is just X
                return coeff * matrices[0][i, j]
    
            indices = [None] * (len(matrices) + 1)
            ind_ranges = [None] * (len(matrices) - 1)
            indices[0] = i
            indices[-1] = j
    
            def f():
                counter = 1
                while True:
                    yield Dummy("i_%i" % counter)
                    counter += 1
    
            dummy_generator = kwargs.get("dummy_generator", f())
    
            for i in range(1, len(matrices)):
                indices[i] = next(dummy_generator)
    
            for i, arg in enumerate(matrices[:-1]):
                ind_ranges[i] = arg.shape[1] - 1
            matrices = [arg._entry(indices[i], indices[i + 1], dummy_generator=dummy_generator) for i, arg in enumerate(matrices)]
            expr_in_sum = Mul.fromiter(matrices)
            if any(v.has(ImmutableMatrix) for v in matrices):
                expand = True
            result = coeff * Sum(
                    expr_in_sum,
                    *zip(indices[1:-1], [0] * len(ind_ranges), ind_ranges)
                )
    
            # Don't waste time in result.doit() if the sum bounds are symbolic
            if not any(isinstance(v, (Integer, int)) for v in ind_ranges):
                expand = False
            return result.doit() if expand else result
        else:
            return self._entry(i)[:, j]

    def as_coeff_matrices(self):
#         scalars = [x for x in self.args if not x.is_Matrix]
#         matrices = [x for x in self.args if x.is_Matrix]
        scalars = [x for x in self.args if not x.shape]
        matrices = [x for x in self.args if x.shape]

        coeff = Mul(*scalars)
#         if coeff.is_commutative == False:
#             raise NotImplementedError("noncommutative scalars in MatMul are not supported.")

        return coeff, matrices

    def as_coeff_mmul(self):
        coeff, matrices = self.as_coeff_matrices()
        return coeff, MatMul(*matrices)

    def _eval_adjoint(self):
        from sympy import Adjoint
        return MatMul(*[Adjoint(arg) for arg in self.args[::-1]]).doit()

    def _eval_trace(self):
        factor, mmul = self.as_coeff_mmul()
        if factor != 1:
            from .trace import trace
            return factor * trace(mmul.doit())
        else:
            raise NotImplementedError("Can't simplify any further")

    def _eval_inverse(self):
        try:
            return MatMul(*[arg.inverse() for arg in self.args[::-1]]).doit()
        except ShapeError:
            from sympy.matrices.expressions.inverse import Inverse
            return Inverse(self)

    def doit(self, **kwargs):
        deep = kwargs.get('deep', False)
        if deep:
            args = [arg.doit(**kwargs) for arg in self.args]
        else:
            args = self.args
        # treat scalar*MatrixSymbol or scalar*MatPow separately
        expr = canonicalize(MatMul(*args))
        return expr

    # Needed for partial compatibility with Mul
    def args_cnc(self, **kwargs):
        return self.args, []
        coeff_c = [x for x in self.args if x.is_commutative]
        coeff_nc = [x for x in self.args if not x.is_commutative]
        return [coeff_c, coeff_nc]

    def _eval_derivative(self, x):
        if self._has(x):
            return
        return MatrixExpr._eval_derivative(self, x)

    def _eval_derivative_matrix_lines(self, x):
        from .transpose import Transpose
        with_x_ind = [i for i, arg in enumerate(self.args) if arg.has(x)]
        lines = []
        for ind in with_x_ind:
            left_args = self.args[:ind]
            right_args = self.args[ind + 1:]

            if right_args:
                right_mat = MatMul.fromiter(right_args)
            else:
                right_mat = Identity(self.shape[1])
            if left_args:
                left_rev = MatMul.fromiter([Transpose(i).doit() if i.is_Matrix else i for i in reversed(left_args)])
            else:
                left_rev = Identity(self.shape[0])

            d = self.args[ind]._eval_derivative_matrix_lines(x)
            for i in d:
                i.append_first(left_rev)
                i.append_second(right_mat)
                lines.append(i)

        return lines

    @classmethod
    def simplify_Equal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a MatMul object!
        """
        if rhs.is_MatMul:
            lhs_args = [*lhs.args]
            rhs_args = [*rhs.args]
            intersect = set(lhs_args) & set(rhs_args)
            if intersect:
                hit = False
                for arg in intersect:
                    if arg.is_invertible:
                        lhs_args.remove(arg)
                        rhs_args.remove(arg)
                        hit = True
                if hit:
                    return self.func(cls(*lhs_args), cls(*rhs_args)).simplify()

    def simplify(self, **_):
        this = any_zeros(self)
        if this != self:
            return this
        
        this = self.simplifyProduct()
        if this is not self:
            return this
            
        return self

    def simplifyProduct(self):
        for i, prod in enumerate(self.args):
            if prod.is_MatProduct:
                before = self.func(*self.args[:i])
                latter = self.args[i + 1:]
                if latter:
                    latter = self.func(*latter)
                else:
                    latter = Identity(self.shape[-1])
                
                _prod = prod.try_absorb_forward(before)
                if _prod:
                    return _prod @ latter
                
                _prod = prod.try_absorb_backward(latter)
                if _prod:
                    return before @ _prod

        return self

    @staticmethod
    def generate_k_limit(A, B, excludes=None, **kwargs):
        if excludes is None:
            excludes = set()
            
        if A.is_Stack or not B.is_Stack:
            return A.generate_int_limit(0, excludes | B.free_symbols, **kwargs)
        
        return B.generate_int_limit(0 if len(B.shape) == 1 else 1, excludes | A.free_symbols, **kwargs)
           
    def expand(self, var=None, deep=True, **_):
        if not deep:
            return MatrixExpr.expand(self)
         
        from sympy.concrete.expr_with_limits import Stack
        from sympy.concrete.summations import Sum
        if len(self.args) > 2:
            matmul = self.func(*self.args[:-1]).expand(var=var, deep=deep) @ self.args[-1]
            # if matmul.is_MatMul:
                # matmul = matmul.expand(var=var, deep=deep)            
            return matmul
        
        A, B = self.args
        if A.is_MatPow:
            return self
        
        if A.is_BlockMatrix:
            if A.axis == 0:
                if B.is_BlockMatrix and len(A.shape) == 1:
                    if len(A.args) == len(B.args):
                        sgm = None
                        for a, b in zip(A.args, B.args):
                            if a.shape:
                                product = a @ b
                                if product.is_MatMul and len(product.args) == 2:
                                    product = product.expand()
                            else:
                                product = a * b
                            if sgm is None:
                                sgm = product
                            else:
                                sgm += product
                        return sgm
                    else:
                        return self
                else: 
                    args = [self.func(arg, B).simplify() for arg in A.args]
                    if deep:
                        args = [arg.expand(deep=True) if arg.is_MatMul else arg for arg in args]
                    return A.func(*args)
            
            elif A.axis == 1 and len(A.shape) == 2:
                if B.is_BlockMatrix:
                    if B.axis == 1 and len(B.shape) == 2:
                        return (B.T @ A.T).expand().T
                    elif B.axis == 0:
                        A_T = A.T
                        if len(A_T.args) == len(B.args):                                
                            sgm = None
                            for a, b in zip(A_T.args, B.args):
                                if len(a.shape) == 1 and len(b.shape) == 1:
                                    n = a.shape[0]
                                    if b.shape[0] == n:
                                        i = a.generate_var(b.free_symbols, integer=True)
                                        j = a.generate_var(b.free_symbols | {i}, integer=True)                                
                                        product = Stack[j:n, i:n](a[i] * b[j]).simplify()
                                    else:
                                        return self
                                else:
                                    if not b.shape:
                                        product = a * b
                                    elif a.rows == b.shape[0]:
                                        product = (a.T @ b).simplify()
                                        if product.is_MatMul and len(product.args) == 2:
                                            X = product.args[1]
                                            if X.is_BlockMatrix and X.axis == 1 and len(X.shape) == 2:
                                                product = product.expand()
                                    else:
                                        return self
                                if sgm is None:
                                    sgm = product
                                else:
                                    sgm += product
                            return sgm
                return self
                
        
        if A.is_Transpose:
            if B.is_Transpose:
                return (B.arg @ A.arg).expand().T
        
        if B.is_BlockMatrix:
            if len(B.shape) == 2 and B.axis == 1:
                return (B.T @ A.T).expand().T
            return self
              
        if A.is_MatProduct:
            return self
        
        kwargs = {'var': var, 'generator': self}
        
        if len(A.shape) == 1 and len(B.shape) > 1 and B.shape[-1].is_Integer:
            k_limit = MatMul.generate_k_limit(A, B, **kwargs)
            k, *_ = k_limit
            
            args = []                    
            if A.shape[0].is_Integer:
                for j in range(B.shape[-1]):
                    args.append(Sum(A[k] * B[k, j], k_limit).doit())
                from sympy import Matrix
                return Matrix(tuple(args))
            else:
                for j in range(B.shape[-1]):
                    args.append(Sum(A[k] * B[k, j], k_limit).simplify())
                return BlockMatrix(*args)
            
        return self

    def _eval_is_extended_integer(self):
        for elem in self.args:
            is_integer = elem.is_extended_integer
            if is_integer:
                continue
            return is_integer
        return True

    @property
    def domain(self):
        interval = self.dtype.universalSet
        if shape := self.shape:
            from sympy import CartesianSpace 
            return CartesianSpace(interval, *shape)
        return interval

    def _sympystr(self, p):
        from sympy.core.mul import _keep_coeff
        from sympy.printing.precedence import precedence
        c, m = self.as_coeff_mmul()
        if c.is_number and c < 0:
            expr = _keep_coeff(-c, m)
            sign = "-"
            level = precedence(expr)
        else:
            sign = ""
            level = precedence(self)

        args = [p.parenthesize(arg, level) for arg in self.args]
        if self.args[0].is_DenseMatrix or self.args[0].is_BlockMatrix:
            if self.args[1].is_DenseMatrix or self.args[1].is_BlockMatrix:
                #sympify the first element
                args[0] = 'S' + args[0]

        return sign + ' @ '.join(args)

    def _lean(self, p):
        from sympy.core.mul import _keep_coeff
        from sympy.printing.precedence import precedence
        c, m = self.as_coeff_mmul()
        if c.is_number and c < 0:
            expr = _keep_coeff(-c, m)
            sign = "-"
            level = precedence(expr)
        else:
            sign = ""
            level = precedence(self)

        args = [p.parenthesize(arg, level) for arg in self.args]
        if self.args[0].is_DenseMatrix or self.args[0].is_BlockMatrix:
            if self.args[1].is_DenseMatrix or self.args[1].is_BlockMatrix:
                #sympify the first element
                args[0] = 'S' + args[0]

        return sign + ' @ '.join(args)

    def _pretty(self, p):
        args = list(self.args)
        from sympy import Add, KroneckerProduct
        from sympy.printing.pretty.stringpict import prettyForm
        for i, a in enumerate(args):
            if (isinstance(a, (Add, KroneckerProduct)) and len(self.args) > 1):
                args[i] = prettyForm(*p._print(a).parens())
            else:
                args[i] = p._print(a)

        return prettyForm.__matmul__(*args)
    
    def _latex(self, p):
        parens = lambda x: r"\left(%s\right)" % p._print(x) if x.is_Add or x.is_Mul else p._print(x)

        args = [*self.args]

        if isinstance(self, MatMul) and self._coeff_isneg():
            if args[0] == -1:
                args = args[1:]
            else:
                args[0] = -args[0]
            return '- ' + r' \times '.join(map(parens, args))
        else:
            return r' \times '.join(map(parens, args))

    def as_ordered_factors(self, **_):
        return [self]

    def _eval_is_extended_real(self):
        return fuzzy_and(arg.is_extended_real for arg in self.args)

    def _eval_is_hyper_real(self):
        return fuzzy_and(arg.is_hyper_real for arg in self.args)
    
    def _eval_is_super_real(self):
        return fuzzy_and(arg.is_super_real for arg in self.args)
    
    def _eval_is_hyper_complex(self):
        return fuzzy_and(arg.is_hyper_complex for arg in self.args)
    
    def _eval_is_extended_positive(self):
        return fuzzy_and(arg.is_extended_positive for arg in self.args)

    def _eval_is_extended_negative(self):
        return fuzzy_and(arg.is_extended_negative for arg in self.args)

    def _eval_is_finite(self):
        if self._has_infinite_dimension():
            return
        return fuzzy_and(arg.is_finite for arg in self.args)

    @classmethod
    def class_key(cls):
        return 3, 0, cls.__name__
    
    @cacheit
    def _has_infinite_dimension(self):
        args = self.args
        for i in range(len(args) - 1):
            expr = args[i]
            s = expr.shape[-1]
            if not isinstance(s, int) and s.is_infinite:
                return True
        
    @property
    def dtype(self):
        dtype = None
        for arg in self.args:
            _dtype = arg.dtype
            if dtype is None or dtype in _dtype:
                dtype = _dtype

        if self._has_infinite_dimension():
            return dtype.extended_type()

        return dtype
    
    @cacheit
    def _eval_domain_defined(self, x, **_):
        if x.dtype.is_set:
            return x.universalSet
        
        domain = x.domain
        for arg in self.args:
            if any(s._has(x) for s in arg.shape):
                kwargs = dict(allow_empty=True)
            else:
                kwargs = {}
            domain &= arg.domain_defined(x, **kwargs)
        return domain
    
    def domain_definition(self, **_):
        eq = MatrixExpr.domain_definition(self)
        for arg in self.args:
            eq &= arg.domain_definition(allow_empty=True)
        return eq

    def _eval_transpose(self, *axis):
        """Transposition of matrix multiplication.

        Notes
        =====

        The following rules are applied.

        Transposition for matrix multiplied with another matrix:
        \\left(A B\\right)^{T} = B^{T} A^{T}

        Transposition for matrix multiplied with scalar:
        \\left(c A\\right)^{T} = c A^{T}

        References
        ==========

        .. [1] https://en.wikipedia.org/wiki/Transpose
        """
        if axis == self.default_axis:
            return self.func(*(arg.T for arg in self.args[::-1]))

    def _subs(self, old, new, **hints):
        if old.is_MatMul:
            args = old.args
            from std.search import sunday
            i = sunday(self.args, args)
            if i >= 0:
                return self.func(*self.args[:i] + (new.args if new.is_MatMul else (new,)) + self.args[i + len(args):]).simplify()
            
        [*args] = self.args
        hit = False
        for i, arg in enumerate(args):
            try:
                arg = arg._subs(old, new)
                if self.args[i] != arg:
                    args[i] = arg
                    hit = True
            except Exception as e:
                if str(e) == 'empty slices':
                    if any(s._has(old) for s in arg.shape):
                        return Zeros(*self.shape)
                
                raise e
        if hit:
            return self.func(*args)
        return self

    @staticmethod
    def simplify_Lamda(self, squeeze=False):
        expr = self.expr
        var = self.limits[0]
        *former, last = expr.args
        if last._has(var) and not any(e._has(var) for e in former):
            last = self.func(last, var)
            _last = last.simplify()
            if last != _last:
                if len(_last.shape) == 2:
                    _last = _last.T
                independent = expr.func(*former, _last).simplify()
                limits = self.limits[1:]
                if limits:
                    independent = self.func(independent, *limits)
                return independent
            
        var = self.limits[-1][0]
        
        first, *latter = expr.args
        if first._has(var) and not any(arg._has(var) for arg in latter):
# consider the complex case:
# [i:n - Min(l, n) + 1](Q[i + Min(l, n) - 1] @ W @ K[i:i + Min(l, n)].T)
            first = self.func(expr.args[0], self.limits[-1])
            _first = first.simplify()
            if first != _first:
                independent = expr.func(_first, *latter).simplify()
                limits = self.limits[:-1]
                if limits:
                    independent = self.func(independent, *limits)
                return independent

        return self
        
    @cacheit
    def sort_key(self, order=None):
        args = self._sorted_args
        args = len(args), tuple(arg.class_key() for arg in args), tuple(arg.sort_key(order=order) for arg in args)
        from sympy import S
        return self.class_key(), args, S.One.sort_key(), S.One

    def _eval_is_extended_complex(self):
        for arg in self.args:
            if arg.is_extended_complex:
                continue

            return
                
        return True

    def _eval_conjugate(self):
        if len(self.shape) < 2:
            return MatMul(*(~arg for arg in self.args), evaluate=False)
        return MatrixExpr._eval_conjugate(self)


def validate(*matrices):
    """ Checks for valid shapes for args of MatMul """
    for i in range(len(matrices) - 1):
        A, B = matrices[i:i + 2]
        if A.cols != B.rows:
            raise ShapeError("Matrices %s and %s are not aligned" % (A, B))

# Rules


def newmul(*args):
    if args[0] == 1:
        args = args[1:]
    return new(MatMul, *args)


def any_zeros(mul):
    if any([arg.is_zero or (arg.is_Matrix and arg.is_Zeros) for arg in mul.args]):
#         matrices = [arg for arg in mul.args if arg.is_Matrix]
        matrices = mul.args
        if len(matrices[0].shape) == 1:
            if len(matrices[-1].shape) == 1:
                from sympy import S
                return S.Zero
            return Zeros(matrices[-1].cols)
        if len(matrices[-1].shape) == 1:
            return Zeros(matrices[0].rows)
        return Zeros(matrices[0].rows, matrices[-1].cols)
    return mul


def merge_explicit(matmul):
    """ Merge explicit MatrixBase arguments

    >>> from sympy import MatrixSymbol, Matrix, MatMul, pprint
    >>> from sympy.matrices.expressions.matmul import merge_explicit
    >>> A = MatrixSymbol('A', 2, 2)
    >>> B = Matrix([[1, 1], [1, 1]])
    >>> C = Matrix([[1, 2], [3, 4]])
    >>> X = MatMul(A, B, C)
    >>> pprint(X)
      [1  1] [1  2]
    A*[    ]*[    ]
      [1  1] [3  4]
    >>> pprint(merge_explicit(X))
      [4  6]
    A*[    ]
      [4  6]

    >>> X = MatMul(B, A, C)
    >>> pprint(X)
    [1  1]   [1  2]
    [    ]*A*[    ]
    [1  1]   [3  4]
    >>> pprint(merge_explicit(X))
    [1  1]   [1  2]
    [    ]*A*[    ]
    [1  1]   [3  4]
    """
    if not any(isinstance(arg, MatrixBase) for arg in matmul.args):
        return matmul
    newargs = []
    last = matmul.args[0]
    for arg in matmul.args[1:]:
        if isinstance(arg, (MatrixBase, Number)) and isinstance(last, (MatrixBase, Number)):
            last = last * arg
        else:
            newargs.append(last)
            last = arg
    newargs.append(last)

    return MatMul(*newargs)


def xxinv(mul):
    """ Y * X * X.I -> Y """
    factor, matrices = mul.as_coeff_matrices()
    for i, (X, Y) in enumerate(zip(matrices[:-1], matrices[1:])):
        try:
            if X.is_square and Y.is_square:
                _X, x_exp = X, 1
                _Y, y_exp = Y, 1
                if X.is_MatPow and not X.is_Inverse:
                    _X, x_exp = X.args
                if Y.is_MatPow and not Y.is_Inverse:
                    _Y, y_exp = Y.args
                if _X == _Y.inverse():
                    if x_exp - y_exp > 0:
                        I = _X ^ (x_exp - y_exp)
                    else:
                        I = _Y ^ (y_exp - x_exp)
                    return newmul(factor, *(matrices[:i] + [I] + matrices[i + 2:]))
        except (ValueError, AttributeError):  # Y might not be invertible
            pass
    return mul


def remove_ids(mul):
    """ Remove Identities from a MatMul

    This is a modified version of sympy.strategies.rm_id.
    This is necesssary because MatMul may contain both MatrixExprs and Exprs
    as args.

    See Also
    ========

    sympy.strategies.rm_id
    """
    # Separate Exprs from MatrixExprs in args
    factor, mmul = mul.as_coeff_mmul()
    # Apply standard rm_id for MatMuls
    result = rm_id(lambda x: x.is_Identity is True)(mmul)
    if result != mmul:
        return newmul(factor, *result.args)  # Recombine and return
    else:
        return mul


def factor_in_front(mul):
    factor, matrices = mul.as_coeff_matrices()
    if factor != 1:
        return newmul(factor, *matrices)
    return mul


def combine_powers(mul):
    # combine consecutive powers with the same base into one
    # e.g. A*A**2 -> A**3
    factor, mmul = mul.as_coeff_mmul()
    args = []
    base = None
    exp = 0
    for arg in mmul.args if mmul.is_MatMul else (mmul,):
        if isinstance(arg, MatPow):
            current_base = arg.args[0]
            current_exp = arg.args[1]
        else:
            current_base = arg
            current_exp = 1
        if current_base == base and len(base.shape) > 1:
            exp += current_exp
        else:
            if not base is None:
                if exp == 1:
                    args.append(base)
                else:
                    args.append(MatPow(base, exp))
            exp = current_exp
            base = current_base
    if exp == 1:
        args.append(base)
    else:
        args.append(MatPow(base, exp))
#         args.append(base ** exp)

    return newmul(factor, *args)


rules = (any_zeros, remove_ids, xxinv, unpack, rm_id(lambda x: x == 1),
         merge_explicit, factor_in_front, flatten, combine_powers)
canonicalize = exhaust(typed({MatMul: do_one(*rules)}))


def only_squares(*matrices):
    """factor matrices only if they are square"""
    if matrices[0].shape[-2] != matrices[-1].shape[-1]:
        raise RuntimeError("Invalid matrices being multiplied")
    out = []
    start = 0
    for i, M in enumerate(matrices):
        if M.shape[-1] == matrices[start].shape[-2]:
            args = matrices[start:i + 1]
            if len(args) == 1:
                mat = args[0]
            else:
                mat = MatMul(*args).doit()
            out.append(mat)
            start = i + 1
    return out


from sympy.assumptions.ask import ask, Q
from sympy.assumptions.refine import handlers_dict


def refine_MatMul(expr, assumptions):
    """
    >>> from sympy import MatrixSymbol, Q, assuming, refine
    >>> X = MatrixSymbol('X', 2, 2)
    >>> expr = X * X.T
    >>> print(expr)
    X*X.T
    >>> with assuming(Q.orthogonal(X)):
    ...     print(refine(expr))
    I
    """
    newargs = []
    exprargs = []

    for args in expr.args:
        if args.is_Matrix:
            exprargs.append(args)
        else:
            newargs.append(args)

    last = exprargs[0]
    for arg in exprargs[1:]:
        if arg == last.T and ask(Q.orthogonal(arg), assumptions):
            last = Identity(arg.shape[0])
        elif arg == last.conjugate() and ask(Q.unitary(arg), assumptions):
            last = Identity(arg.shape[0])
        else:
            newargs.append(last)
            last = arg
    newargs.append(last)

    return MatMul(*newargs)


handlers_dict['MatMul'] = refine_MatMul
