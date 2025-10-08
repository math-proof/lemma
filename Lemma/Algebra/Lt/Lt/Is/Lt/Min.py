from util import *


@apply
def apply(lt_a, lt_b):
    x, a = lt_a.of(Less)
    S[x], b = lt_b.of(Less)
    return x < Min(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(x < y, x < b)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.LtMin.of.Lt.Lt)

    Eq << Eq[-1].this.rhs.apply(Algebra.Lt.Lt.given.Lt.Min)




if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-05-21
