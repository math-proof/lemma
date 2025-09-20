from sympy import Basic
from sympy.functions import conjugate

from sympy.matrices.expressions.matexpr import MatrixExpr
from sympy.core.sympify import _sympify
from sympy.core.cache import cacheit
from sympy.core.containers import Tuple


class Transpose(MatrixExpr):
    """
    The transpose of a matrix expression.
    This is a symbolic object that simply stores its argument without
    evaluating it. To actually compute the transpose, use the ``transpose()``
    function, or the ``.T`` attribute of matrices.

    the definition of field self.axis is as follows:
    i, j = self.axis
    if j > 0:
#       self.shape = *self.shape[:i], self.shape[i], *self.shape[i + 1:i + j], *self.shape[i + j]
                                      -------------------swap----------------
        self.shape = *self.shape[:i] + self.shape[i + 1:i + j], self.shape[i], *self.shape[i + j]
    elif j < 0:
#       self.shape = *self.shape[:i + j], *self.shape[i + j:i], self.shape[i], *self.shape[i + 1:]
                                          ---------------swap----------------
        self.shape = *self.shape[:i + j], self.shape[i], *self.shape[i + j:i] + self.shape[i + 1:]
    """

    @property
    def dtype(self):
        return self.arg.dtype

    def __new__(cls, *args, **kwargs):
        if len(args) > 1 and isinstance(args[-1], tuple):
            arg, [i], [j] = args
            axis = i, j
        else:
            arg, = args
            axis = kwargs.pop('axis', (-2, 1))

        arg = _sympify(arg)
        axis = arg.normalize_axis(axis)
                
        if kwargs.get('evaluate', True):
            transpose = arg._eval_transpose(*axis)
            if transpose is not None:
                return transpose

        obj = MatrixExpr.__new__(cls, arg, **kwargs)
        obj.axis = Tuple(*axis)
        return obj
    
    def _sympystr(self, p):
        from sympy.printing.precedence import PRECEDENCE
        if self.axis == self.default_axis:
            return "%s.T" % p.parenthesize(self.arg, PRECEDENCE["Pow"])

        return "Transpose[%s](%s)" % (','.join(p._print(a) for a in self.axis), self.arg)

    def _lean(self, p):
        from sympy.printing.precedence import PRECEDENCE
        if self.axis == self.default_axis:
            return "%s.T" % p.parenthesize(self.arg, PRECEDENCE["Pow"])

        return "Transpose[%s](%s)" % (','.join(p._print(a) for a in self.axis), self.arg)
    
    def need_parenthesis_for_arg(self):
        arg = self.arg
        return arg.is_ExprWithLimits or arg.is_AssocOp or arg.is_MatMul
    
    def _print_arg(self, p):
        latex = p._print(self.arg)
        if self.need_parenthesis_for_arg():
            latex = r"\left(%s\right)" % latex
        return latex
    
    def _latex(self, p):
        def join(axis):
            op = '+' if axis[1] > 0 else '-'
            return op.join(p._print(a) for a in axis)

        if self.arg.is_Transpose:
            axis = [self.arg.axis, self.axis]
            arg = self.arg
            raise NotImplementedError
            return r"{%s}^{{\color{magenta} T}_{%s}}" % (arg._print_arg(p), ",".join(join(a) for a in axis))
        
        if self.axis == self.default_axis:
            if self.arg.is_BlockMatrix:
                X = self.arg
                return r"{\left(\begin{array}{%s}%s\end{array}\right)}" % ('c' * len(X.args), ' & '.join('{%s}' % p._print(arg.T) for arg in X.args))
            else:
                return r"{%s}^{\color{magenta} T}" % self._print_arg(p)
        else:
            return r"{%s}^{{\color{magenta} T}_{%s}}" % (self._print_arg(p), join(self.axis))
            

    def doit(self, **hints):
        arg = self.arg
        if hints.get('deep', True) and isinstance(arg, Basic):
            arg = arg.doit(**hints)
        _eval_transpose = getattr(arg, '_eval_transpose', None)
        if _eval_transpose is not None:
            result = _eval_transpose()
            return result if result is not None else self
        else:
            return self

    @property
    def arg(self):
        return self.args[0]

    @cacheit
    def _eval_shape(self):
        [*shape] = self.arg.shape
        start, offset = self.axis
        stop = start + offset
        shape.insert(stop, shape.pop(start))
        return tuple(shape)

    def _entry(self, i, j=None, expand=False, **kwargs):
        if self.axis == self.default_axis:
            if j is None:
                if len(self.shape) > 2:
                    return self.arg[i].T
                
                if isinstance(i, Tuple):
                    size = self.shape[0]
                    start, stop, step = i.slice_args
                    if start == 0 and stop == size and step == 1:
                        return self
                    
                    from sympy import Sliced                    
                    return Sliced(self.arg, Tuple(0, self.arg.shape[0]), Tuple(start, stop))
                return self.arg[:, i]
                        
            if hasattr(self.arg, '_entry'):
                return self.arg._entry(j, i, expand=expand, **kwargs)
            
            if isinstance(i, Tuple):
                if isinstance(j, Tuple): 
                    return self.arg[j, i].T
                else:
                    return self.arg[j, i].T
            else:
                return self.arg[j, i]
        else:
            if self.axis == (0, 1):
                if j is None:
                    return self.arg[:, i]
            raise Exception('unimplemented')

    def _eval_adjoint(self):
        return conjugate(self.arg)

    def _eval_conjugate(self):
        from sympy import Adjoint
        return Adjoint(self.arg)

    def _eval_transpose(self, *axis):
        start, offset = axis
        self_start, self_offset = self.axis
        if start == self_start and offset == self_offset == 1 or \
            offset == -self_offset and start + offset == self_start:
            return self.arg
        if self_start + self_offset == start:
            return Transpose[self_start, self_offset + offset](self.arg)

    def _eval_trace(self):
        from .trace import Trace
        return Trace(self.arg)  # Trace(X.T) => Trace(X)

    def _eval_determinant(self, **kwargs):
        from sympy.matrices.expressions.determinant import det
        return det(self.arg)

    def _eval_is_extended_real(self):
        return self.arg.is_extended_real
    
    def _eval_is_hyper_real(self):
        return self.arg.is_hyper_real
    
    def _eval_is_super_real(self):
        return self.arg.is_super_real
    
    def _eval_is_hyper_complex(self):
        return self.arg.is_hyper_complex
    
    def _eval_is_extended_positive(self):
        return self.arg.is_extended_positive
    
    def _eval_is_extended_negative(self):
        return self.arg.is_extended_negative
    
    def _eval_is_finite(self):
        return self.arg.is_finite

    def _eval_derivative_matrix_lines(self, x):
        lines = self.args[0]._eval_derivative_matrix_lines(x)
        return [i.transpose() for i in lines]

    @classmethod
    def simplify_Equal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a Transpose object!
        """
        if rhs.is_Transpose:
            return self.func(lhs.arg, rhs.arg)

    def simplify(self, **_):
        from sympy.core.function import Function
        from sympy.core.mul import Mul
        f = self.arg
        if isinstance(f, Function):
            if len(f.shape) > 1:
                return self
            return f.func(self.func(f.arg).simplify())
        if isinstance(f, Mul):
            if len(f.args[0].shape) == 0:
                return f.func(f.args[0], self.func(f.func(*f.args[1:])).simplify())

        return self

    @cacheit
    def _eval_domain_defined(self, x, **_):
        domain = MatrixExpr._eval_domain_defined(self, x)
        for arg in self.args:
            domain &= arg.domain_defined(x)
        return domain

    def _subs(self, old, new, **hints):
        this = self.arg
        if this.is_BlockMatrix and old.is_Transpose and old.arg.is_BlockMatrix:
            args = old.arg.args
            from std.search import sunday
            i = sunday(this.args, args)
            if i >= 0:
                return this.func(*this.args[:i] + (new.T,) + this.args[i + len(args):]).simplify().T
                
        return MatrixExpr._subs(self, old, new, **hints)

    def __getitem__(self, indices):
        if (indices := self.simplify_indices(indices)) is None:
            return self
        
        if isinstance(indices, Tuple):
            return self._entry(indices)

        if isinstance(indices, tuple):
            if len(indices) == 1:
                indices = indices[0]
            elif len(indices) == 2:
                i, j = indices
                if isinstance(i, Tuple):
                    if isinstance(j, Tuple):
                        return self._entry(i, j)
                    else:
                        return self.func(self.arg[j])

                i, j = _sympify(i), _sympify(j)
                if self.valid_index(i, j) != False:
                    return self._entry(i, j)
                else:
                    raise IndexError("Invalid indices (%s, %s)" % (i, j))

            else:
                indices = [*indices]
                axis, offset = self.axis
                start, offset = axis + offset, -offset
                stop = start + offset
                min_length = max(start + 1, stop - 1)
                if len(indices) < min_length:
                    indices += [slice(None)] * (min_length - len(indices))
                indices.insert(stop, indices.pop(start))
                return self.arg[tuple(indices)]

        assert isinstance(indices, int) or indices.is_Expr
        return self._entry(indices)

    def of(self, cls):
        if cls.is_IndexedOperator:
            if cls.func.is_Transpose:
                if len(cls.limits) == 1:
                    [limit] = cls.limits
                    if len(limit) == 1:
                        [axis] = limit
                        if axis == self.axis:
                            return self.args
                        
                if self.axis == self.default_axis:
                    return MatrixExpr.of(self, cls)
                    
        elif isinstance(cls, type):
            if cls.is_Transpose:
                if self.axis == self.default_axis:
                    return self.arg
            
            elif isinstance(self, cls):
                return self
            
        elif cls.is_Transpose:#of Basic type
            axis = cls.kwargs.get('axis', self.default_axis)
            if axis == self.axis:
                if cls.args:
                    return MatrixExpr.of(self, cls)
                else:
                    return self.args
    
    @staticmethod
    def expand_dims(self, shape, pivot):
        consistent_shape = shape[:-pivot] 
        consistent_shape_len = len(consistent_shape)

        extra_shape = shape[-pivot:]        
        extra_shape_len = len(extra_shape)
        # transpose matrix from (*consistent_shape, *extra_shape) to (*extra_shape, *consistent_shape)
        # (3, 4, 5, 6) => (5, 6, 3, 4)
        axes = []
        if extra_shape_len % consistent_shape_len == 0:
            for j in range(extra_shape_len):
                axes.append((j, j + consistent_shape_len))
        elif consistent_shape_len % extra_shape_len == 0:
            for j in reversed(range(consistent_shape_len)):
                axes.append((j, j + extra_shape_len))
        else:
            raise UnimplementedError('Unimplemented')
        # for j in range(extra_shape_len):
        #     # axes.append((j, j + consistent_shape_len))
        #     for i in range(consistent_shape_len):
        #         axes.append(consistent_shape_len + j - i)

        if len(self.shape) < len(shape):
            from sympy import Ones
            self *= Ones(*extra_shape, *consistent_shape)

        for axis in axes:
            self = Transpose[axis](self)
        return self

    def _hashable_content(self):
        return super()._hashable_content() + self.axis

    @property
    def kwargs(self):
        return {'axis': self.axis}


def transpose(expr, *args):
    """Matrix transpose"""
    if not args:
        args = (-2, -1)
    i, j = args
    return Transpose[i, j](expr).doit(deep=False)


from sympy.assumptions.ask import ask, Q
from sympy.assumptions.refine import handlers_dict


def refine_Transpose(expr, assumptions):
    """
    >>> from sympy import MatrixSymbol, Q, assuming, refine
    >>> X = MatrixSymbol('X', 2, 2)
    >>> X.T
    X.T
    >>> with assuming(Q.symmetric(X)):
    ...     print(refine(X.T))
    X
    """
    if ask(Q.symmetric(expr), assumptions):
        return expr.arg

    return expr


handlers_dict['Transpose'] = refine_Transpose
