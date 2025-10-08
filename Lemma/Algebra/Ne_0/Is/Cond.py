from util import *


@apply
def apply(given):
    cond, S[0] = given.of(Unequal[Bool])
    return cond


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    a, b = Symbol(real=True)
    Eq << apply(Unequal(functions.Bool(a > b), 0))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Cond.of.Ne_0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ne_0.given.Cond)




if __name__ == '__main__':
    run()
# created on 2023-11-05
