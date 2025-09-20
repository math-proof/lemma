from util import *


@apply
def apply(given):
    lhs, rhs = given.of(GreaterEqual)
    assert rhs > 0

    return GreaterEqual(log(lhs), log(rhs))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(real=True)
    y = Symbol(positive=True)
    Eq << apply(GreaterEqual(x, y))

    Eq << Eq[1].this.apply(Algebra.Ge.given.Ge_0)

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Log)

    Eq.is_nonnegative = Eq[0] / y - 1

    t = Symbol(nonnegative=True)
    Eq << GreaterEqual(log(1 + t), 0, plausible=True)

    Eq << Logic.All.of.Cond.apply(Eq[-1], t)

    t = Eq[-1].variable
    Eq << Logic.Imp.of.AllSetOf.apply(Eq[-1])

    Eq << Eq[-1].subs(t, Eq.is_nonnegative.lhs)
    Eq << Logic.Cond.of.Imp.Cond.apply(Eq.is_nonnegative, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-05-26
