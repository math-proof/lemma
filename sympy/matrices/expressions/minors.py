from sympy.core.sympify import _sympify
from sympy.core import Basic
from sympy.matrices.expressions.matexpr import MatrixExpr
from sympy.core.cache import cacheit


class Minors(MatrixExpr):
    """
    The minors of a matrix expression

    This is a symbolic object that simply stores its argument without
    evaluating it. To actually compute the minors, use the ``.minors()``
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
            return self.arg._eval_minors()
        except:
            return self
    
    def _entry(self, i, j=None, **_):
        from sympy.concrete.expr_with_limits import Stack
        from sympy.matrices.expressions.determinant import Det
        m, n = self.rows, self.cols
        if j is None:
            j = self.generate_var(integer=True)
            return Stack[j:n](Det(self.arg.drop(m - 1 - i, n - 1 - j)))
        return Det(self.arg.drop(m - 1 - i, n - 1 - j))

# Needs["Combinatorica`"]
# mat = Array[Subscript[A, ##] &, {10, 10}, 0]
# Block[{i = 3, j = 7}, 
#  Cofactor[mat, {i, j}] == 
#   Map[Reverse, Minors[mat], {0, 1}][[i, j]]*(-1)^(i + j)]
