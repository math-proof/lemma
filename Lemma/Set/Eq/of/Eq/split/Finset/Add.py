from util import *


@apply
def apply(given):
    (x, y), S[{0, 1}] = given.of(Equal[FiniteSet])

    return Equal(x + y, 1)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic, Bool
    x, y = Symbol(integer=True)

    Eq << apply(Equal({x, y}, {0, 1}))

    Eq << Algebra.EqReducedSum.of.Eq.apply(Eq[0])

    Eq << Eq[-1].this.rhs.doit()

    Eq << Eq[-1].this.lhs.doit()

    Eq << Set.Ne.of.Eq.apply(Eq[0])

    Eq << Bool.BFn.of.BFnIte.Cond.apply(Eq[-1], Eq[-2])

if __name__ == '__main__':
    run()

# created on 2020-08-27
