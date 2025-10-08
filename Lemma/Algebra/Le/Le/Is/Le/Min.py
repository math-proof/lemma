from util import *


@apply
def apply(le_a, le_b):
    x, a = le_a.of(LessEqual)
    S[x], b = le_b.of(LessEqual)
    return x <= Min(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(x <= y, x <= b)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.LeMin.of.Le.Le)

    Eq << Eq[-1].this.rhs.apply(Algebra.Le.Le.given.Le.Min)




if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-05-21
