from util import *


@apply
def apply(given):
    x = given.of(Expr >= 0)
    return Equal(Min(x, 0), 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Nat
    x = Symbol(real=True)

    Eq << apply(x >= 0)

    Eq << Eq[-1].this.lhs.apply(Nat.Min.eq.IteLe)

    Eq << Bool.And_BFnIte.given.And_BFn.apply(Eq[0], Eq[-1], reverse=True)


if __name__ == '__main__':
    run()
# created on 2019-05-27
