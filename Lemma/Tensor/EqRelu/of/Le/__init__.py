from util import *


@apply
def apply(le, m):
    k, n = le.of(LessEqual)
    return Equal(relu(k - Min(m, n)), relu(k - m))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra

    k, n, m = Symbol(integer=True)
    Eq << apply(k <= n, m)

    Eq << Eq[1].this.lhs.apply(Tensor.Relu.eq.Add.Min)

    Eq << Eq[-1].this.rhs.apply(Tensor.Relu.eq.Add.Min)

    Eq << Algebra.EqMin.of.Le.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1].reversed)



if __name__ == '__main__':
    run()
# created on 2021-12-25

del Le
del Ge
from . import Le
from . import Ge
