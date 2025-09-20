from util import *


@apply
def apply(x):
    from Lemma.Discrete.Alpha.gt.Zero import alpha
    from Lemma.Discrete.K.eq.Add.definition import K
    n = x.shape[0]
    n -= 1
    assert n >= 1
    return Equal(alpha(x[:n + 1]), alpha(x[:n]) + (-1) ** (n + 1) / (K(x[:n + 1]) * K(x[:n])))


@prove
def prove(Eq):
    from Lemma import Discrete
    from Lemma.Discrete.Alpha.gt.Zero import alpha

    x = Symbol(real=True, positive=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)

    Eq << apply(x[:n + 1])

    Eq << Eq[0].this.lhs.apply(Discrete.Alpha.eq.DivH_K.positive)

    Eq << Eq[-1].this.find(alpha).apply(Discrete.Alpha.eq.DivH_K.positive)

    Eq << Eq[-1] - Eq[-1].rhs.args[0]

    Eq << Eq[-1].this.lhs.together()

    Eq << Discrete.Add.eq.Pow.HK.recurrence.apply(x[:n + 1])


if __name__ == '__main__':
    run()

# created on 2020-09-26

from . import step2
