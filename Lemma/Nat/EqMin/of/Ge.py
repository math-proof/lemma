from util import *


@apply
def apply(given, reverse=False):
    a, b = given.of(GreaterEqual)
    if reverse:
        return Equal(b, Min(a, b))
    return Equal(Min(a, b), b)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Nat

    x, y = Symbol(real=True, given=True)
    Eq << apply(x >= y)

    Eq << Eq[-1].this.lhs.apply(Nat.Min.eq.IteLt)

    Eq << Eq[-1].this.lhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite)

    Eq << Bool.And_BFnIte.given.And_BFn.apply(Eq[0], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2018-09-04
# updated on 2023-06-23
