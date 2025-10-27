from util import *


@apply
def apply(equality, inequality):
    lhs, rhs = equality.of(Equal)
    x = inequality.of(Unequal[Pr, 0])

    _x, y = lhs.of(Pr).args

    if x != _x:
        S[x], y = y, _x

    assert rhs == Pr(x) * Pr(y)
    return Equal(Pr(y, given=x), Pr(y))


@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Bool, Nat

    x, y = Symbol(real=True, random=True)
    given = Equal(Pr(x, y), Pr(x) * Pr(y))
    Eq << apply(given, Unequal(Pr(x), 0))

    Eq << Eq[-1].simplify()

    Eq << Probability.Pr.eq.Mul.Pr.of.Ne_0.bayes.apply(Eq[1], y)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1] - Eq[-1].rhs

    Eq << Eq[-1].this.lhs.collect(Pr(x))

    Eq << Nat.OrEqS_0.of.Mul.eq.Zero.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[1]

    Eq << Bool.And_And.of.And.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-07-15
