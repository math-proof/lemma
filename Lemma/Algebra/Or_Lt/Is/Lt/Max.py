from util import *


@apply
def apply(given):
    (x, a), (S[x], b) = given.of(Less | Less)
    return Less(x, Max(a, b))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(Less(x, a) | Less(x, b))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(Algebra.Or.Lt.of.Lt_Max)

    Eq << Eq[-2].this.rhs.apply(Algebra.Lt_Max.given.Or.Lt)


if __name__ == '__main__':
    run()
# created on 2022-01-02
