from util import *


@apply
def apply(given):
    cond, S[0] = given.of(Equal[Bool])
    return cond.invert()


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    a, b = Symbol(real=True)
    Eq << apply(Equal((a > b).toNat, 0))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Cond.of.Eq_0.invert)

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq_0.given.Cond.invert)




if __name__ == '__main__':
    run()
# created on 2023-11-05
