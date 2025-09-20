from util import *


@apply
def apply(le, ge):
    x, y = le.of(LessEqual)
    S[x], S[-y] = ge.of(GreaterEqual)
    return LessEqual(abs(x), y)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    y, x = Symbol(real=True)
    Eq << apply(x <= y, x >= -y)

    Eq << Eq[-1].this.lhs.apply(Algebra.Abs.eq.IteGe_0)

    Eq << Eq[-1].apply(Logic.BFn_Ite.given.OrAndS)

    Eq << Logic.Cond.BFnIte.given.And_BFn.apply(Eq[0], Eq[-1])

    Eq << -Eq[1]

    Eq << Logic.Cond.BFnIte.given.And_BFn.apply(Eq[-1], Eq[-2])





if __name__ == '__main__':
    run()
# created on 2018-06-27
# updated on 2023-08-26
from . import both
