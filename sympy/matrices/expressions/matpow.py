from .matexpr import MatrixExpr, Identity, Zeros
from ..common import ShapeError
from sympy.core import S

from sympy.core.sympify import _sympify
from sympy.matrices import MatrixBase
from sympy.core.cache import cacheit


class MatPow(MatrixExpr):
    precedence = 4
    
    @property
    def is_Inverse(self):
        return self.exp is S.NegativeOne
    
    def __new__(cls, base, exp):
        base = _sympify(base)
        assert base.is_square, str(base)
#         if not base.is_Matrix:
#             raise TypeError("Function parameter should be a matrix")
        exp = _sympify(exp)
        
        if base.is_MatPow:
            base, e = base.args
            exp *= e

        if exp.is_zero:
            return Identity(base.shape[-1])
        elif exp.is_One:
            return base
        
        return super(MatPow, cls).__new__(cls, base, exp)

    @property
    def base(self):
        return self.args[0]

    @property
    def exp(self):
        return self.args[1]

    def _eval_shape(self):
        return self.base.shape

    def _entry(self, i, j=None, **kwargs):
        from sympy.matrices.expressions import MatMul
        A = self.doit()
        if isinstance(A, MatPow):
            # We still have a MatPow, make an explicit MatMul out of it.
            if not A.base.is_square:
                raise ShapeError("Power of non-square matrix %s" % A.base)
            elif A.exp.is_Integer and A.exp.is_positive:
                if j is None:
                    return A.func(A.base, A.exp - 1)[i] @ A.base
                A = MatMul(*[A.base for k in range(A.exp)])
            # elif A.exp.is_Integer and self.exp.is_negative:
            # Note: possible future improvement: in principle we can take
            # positive powers of the inverse, but carefully avoid recursion,
            # perhaps by adding `_entry` to Inverse (as it is our subclass).
            # T = A.base.as_explicit().inverse()
            # A = MatMul(*[T for k in range(-A.exp)])
            else:
                # Leave the expression unevaluated:
                from sympy.matrices.expressions.matexpr import MatrixElement
                return MatrixElement(self, i, j)
        return A._entry(i, j)

    def doit(self, **kwargs):
        from sympy.matrices.expressions import Inverse
        deep = kwargs.get('deep', True)
        if deep:
            args = [arg.doit(**kwargs) for arg in self.args]
        else:
            args = self.args

        base, exp = args
        # combine all powers, e.g. (A**2)**3 = A**6
        while isinstance(base, MatPow):
            exp = exp * base.args[1]
            base = base.args[0]

        if exp.is_zero and base.is_square:
            if isinstance(base, MatrixBase):
                return base.func(Identity(base.shape[0]))
            return Identity(base.shape[0])
        elif isinstance(base, Zeros) and exp.is_negative:
            raise ValueError("Matrix determinant is 0, not invertible.")
        elif base.is_Identity or isinstance(base, Zeros):
            return base
        elif isinstance(base, MatrixBase) and exp.is_number:
            if exp is S.One:
                return base
            return base ** exp
        # Note: just evaluate cases we know, return unevaluated on others.
        # E.g., MatrixSymbol('x', n, m) to power 0 is not an error.
        elif exp is S(-1) and base.is_square:
            if self.base == base:
                return self

            return Inverse(base).doit(**kwargs)
        elif exp is S.One:
            return base
        return MatPow(base, exp)

    def _eval_transpose(self, *axis):
        if axis == self.default_axis:
            base, exp = self.args
            return MatPow(base.T, exp)

    def _eval_derivative_matrix_lines(self, x):
        from sympy.core.expr import ExprBuilder
        from sympy.codegen.array_utils import CodegenArrayContraction, CodegenArrayTensorProduct
        from .matmul import MatMul
        from .inverse import Inverse
        exp = self.exp
        if self.base.shape == (1, 1) and not exp.has(x):
            lr = self.base._eval_derivative_matrix_lines(x)
            for i in lr:
                subexpr = ExprBuilder(
                    CodegenArrayContraction,
                    [
                        ExprBuilder(
                            CodegenArrayTensorProduct,
                            [
                                Identity(1),
                                i._lines[0],
                                exp * self.base ** (exp - 1),
                                i._lines[1],
                                Identity(1),
                            ]
                        ),
                        (0, 3, 4), (5, 7, 8)
                    ],
                    validator=CodegenArrayContraction._validate
                )
                i._first_pointer_parent = subexpr.args[0].args
                i._first_pointer_index = 0
                i._second_pointer_parent = subexpr.args[0].args
                i._second_pointer_index = 4
                i._lines = [subexpr]
            return lr
        if (exp > 0) == True:
            newexpr = MatMul.fromiter([self.base for i in range(exp)])
        elif (exp == -1) == True:
            arg = self.args[0]
            lines = arg._eval_derivative_matrix_lines(x)
            for line in lines:
                line.first_pointer *= -self.T
                line.second_pointer *= self
            return lines
#             return Inverse(self.base)._eval_derivative_matrix_lines(x)
        elif (exp < 0) == True:
            newexpr = MatMul.fromiter([Inverse(self.base) for i in range(-exp)])
        elif (exp == 0) == True:
            return self.doit()._eval_derivative_matrix_lines(x)
        else:
            raise NotImplementedError("cannot evaluate %s derived by %s" % (self, x))
        return newexpr._eval_derivative_matrix_lines(x)

    def _eval_inverse(self):
        if self.exp is S.NegativeOne:
            return self.base

    def _eval_determinant(self, **kwargs):
        from sympy.matrices.expressions.determinant import det
        return det(self.base) ** self.exp

    @property
    def dtype(self):
        return self.base.dtype

    def _sympystr(self, p):
#         deliberately to distinguish from x ** y which is element-wise power operator
        lhs, rhs = self.args
        _lhs = p._print(lhs)
        if lhs.is_Add or lhs.is_Mul or lhs.is_MatMul:
            _lhs = "(%s)" % _lhs
            
        _rhs = p._print(rhs)
        if rhs.is_Add or rhs.is_Mul or rhs.is_MatMul:
            _rhs = "(%s)" % _rhs
            
        if lhs.is_DenseMatrix or lhs.is_BlockMatrix:
            if rhs.is_Integer:
                _lhs = 'S' + _lhs

        return '%s ^ %s' % (_lhs, _rhs)

    def _lean(self, p):
#         deliberately to distinguish from x ** y which is element-wise power operator
        lhs, rhs = self.args
        _lhs = p._print(lhs)
        if lhs.is_Add or lhs.is_Mul or lhs.is_MatMul:
            _lhs = "(%s)" % _lhs
            
        _rhs = p._print(rhs)
        if rhs.is_Add or rhs.is_Mul or rhs.is_MatMul:
            _rhs = "(%s)" % _rhs
            
        if lhs.is_DenseMatrix or lhs.is_BlockMatrix:
            if rhs.is_Integer:
                _lhs = 'S' + _lhs

        return '%s ^ %s' % (_lhs, _rhs)

    def _latex(self, p):
        base, exp = self.base, self.exp
        if base.is_symbol or base.is_BlockMatrix or base.is_DenseMatrix or base.is_Function:
            return r"%s^{\color{magenta} %s}" % (p._print(base), p._print(exp))
        else:
            return r"\left(%s\right)^{\color{magenta} %s}" % (p._print(base), p._print(exp))

    def domain_definition(self, **_):
        if self.exp.is_extended_negative:
            from sympy import Unequal
            base = self.base
            if base.is_singular == False:
                return S.true
            return Unequal(base.det(), S.Zero)
        return MatrixExpr.domain_definition(self)
    
    def _eval_is_singular(self):
        exp = self.exp
        if exp.is_Integer and exp < 0:
            return False

    def _eval_is_finite(self):
        exp = self.exp
        if exp.is_Integer and exp < 0:
            return True
