from util import *


@apply
def apply(self, var=None, *, simplify=True):
    A, B = self.of(MatMul)
    kwargs = {'var': var, 'generator': self}

    size, = A.shape
    assert len(B.shape) <= 2
    k_limit = MatMul.generate_k_limit(A, B, **kwargs)
    k, *ab = k_limit
    expr = A[k] * B[k]
    if not ab:
        rgn = expr.domain_defined(k)
        if rgn.is_Range:
            if rgn.start != 0 or rgn.stop != size:
                k_limit = (k, 0, size)

    rhs = Sum(expr, k_limit)
    if simplify:
        rhs = rhs.simplify()
    return Equal(self, rhs, evaluate=False)


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    A, B = Symbol(shape=(n,), complex=True)
    Eq << apply(A @ B)





if __name__ == '__main__':
    run()
# created on 2019-11-09
# updated on 2023-05-22
from . import Dot
