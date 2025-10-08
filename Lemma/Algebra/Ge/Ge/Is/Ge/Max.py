from util import *


@apply
def apply(ge_a, ge_b):
    x, a = ge_a.of(GreaterEqual)
    S[x], b = ge_b.of(GreaterEqual)
    return x >= Max(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(x >= y, x >= b)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.GeMax.of.Ge.Ge)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ge.Ge.given.Ge.Max)




if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-05-21
