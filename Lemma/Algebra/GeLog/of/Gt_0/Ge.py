from util import *


@apply
def apply(is_positive, ge):
    x = is_positive.of(Expr > 0)
    lhs, rhs = ge.of(GreaterEqual)
    assert rhs == x
    return GreaterEqual(log(lhs), log(rhs))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, b = Symbol(real=True)
    Eq << apply(b > 0, x >= b)

    t = Symbol(positive=True)
    Eq << (x >= t).this.apply(Algebra.GeLog.of.Ge)

    Eq << Bool.Or.of.ImpNot.apply(Eq[-1])

    Eq << Algebra.Or.of.Cond.subst.apply(Eq[-1], t, b)

    Eq << Bool.Cond.of.Or_Not.Cond.apply(Eq[0], Eq[-1])

    Eq << Bool.Cond.of.Or_Not.Cond.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-08-08
