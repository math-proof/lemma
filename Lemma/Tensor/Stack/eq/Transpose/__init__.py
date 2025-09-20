from util import *


@apply
def apply(self, axis=(-2, 1), *, simplify=True):
    axis = self.normalize_axis(axis)
    if axis == self.default_axis:
        f, *limits = self.of(Stack)
        limits = [*limits]
        if f.shape:
            indices, limits_i = f.variables_with_limits()
            f = f[tuple(indices)]
            limits = limits_i + limits

        limits[0], limits[1] = limits[1], limits[0]
        expr = Stack(f, *limits).simplify()

    elif axis == (0, 1):
        f, *limits, j_limit, i_limit = self.of(Stack)
        expr = Stack(f, *limits, i_limit, j_limit).simplify()

    if simplify:
        rhs = Transpose[axis](expr)
    else:
        rhs = Transpose[axis](expr, evaluate=False)
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    i, j, k = Symbol(integer=True)
    n, m = Symbol(integer=True, positive=True)
    h = Symbol(real=True, shape=(oo, m))
    Eq << apply(Stack[j:n, i:m](h[j + k, i]))

    i = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)



if __name__ == '__main__':
    run()
# created on 2022-01-11

# updated on 2022-03-30
from . import Block
