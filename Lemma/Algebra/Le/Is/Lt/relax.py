from util import *


@apply
def apply(given):
    lhs, rhs = given.of(LessEqual)
    assert lhs.is_integer
    return Less(lhs, rhs + 1)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, y = Symbol(integer=True)
    Eq << apply(x <= y)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Lt.of.Le.relax)

    Eq << Eq[-1].this.rhs.apply(Algebra.Le.given.Lt.relax)


if __name__ == '__main__':
    run()
# created on 2023-11-05
