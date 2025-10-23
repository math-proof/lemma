from util import *


@apply
def apply(lt, gt):
    x, y = lt.of(Less)
    S[x], S[-y] = gt.of(Greater)
    return Less(abs(x), y)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Int

    y, x = Symbol(real=True)
    Eq << apply(x < y, x > -y)

    Eq << Eq[-1].this.lhs.apply(Int.Abs.eq.IteGe_0)

    Eq << Eq[-1].apply(Bool.BFn_Ite.given.OrAndS)

    Eq << Bool.Cond.BFnIte.given.And_BFn.apply(Eq[0], Eq[-1])

    Eq << -Eq[1]

    Eq << Bool.Cond.BFnIte.given.And_BFn.apply(Eq[-1], Eq[-2])





if __name__ == '__main__':
    run()

# created on 2018-07-29
# updated on 2023-08-26

from . import both
