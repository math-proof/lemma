from sympy.core.sympify import _sympify
from sympy.core import Basic
from sympy.matrices.expressions.matexpr import MatrixExpr


class Cofactors(MatrixExpr):
    """
    The cofactors of a matrix expression

    This is a symbolic object that simply stores its argument without
    evaluating it. To actually compute the minors, use the ``.cofactors()``
    method of matrices.

    """

    def __new__(cls, mat): 
        mat = _sympify(mat)
        return Basic.__new__(cls, mat)

    @property
    def arg(self):
        return self.args[0]

    def _eval_shape(self):
        return self.arg.shape
    
    def doit(self, **hints):
        try:
            return self.arg.cofactor_matrix()
        except:
            return self

    @property
    def dtype(self):
        return self.arg.dtype

    def _entry(self, i, j=None, **_):
        from sympy.matrices.expressions.minors import Minors
        from sympy.concrete.expr_with_limits import Stack
        m, n = self.rows, self.cols
        if j is None:
            j = self.generate_var(integer=True)
            return Stack[j:n]((-1) * (i + j) * Minors(self.arg)[m - 1 - i, n - 1 - j])
        return (-1) ** (i + j) * Minors(self.arg)[m - 1 - i, n - 1 - j]

# Needs["Combinatorica`"]
# mat = Array[Subscript[A, ##] &, {5, 5}, 0]
# Block[{i = 3, j = 7}, 
#  Cofactor[mat, {i, j}] == 
#   Map[Reverse, Minors[mat], {0, 1}][[i, j]]*(-1)^(i + j)]
