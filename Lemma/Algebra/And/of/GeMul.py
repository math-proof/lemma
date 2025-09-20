from util import *


@apply
def apply(given):
    factor, cond = given.of(GreaterEqual[Mul[Bool], 1])
    return factor >= 1, cond


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, y = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(GreaterEqual(Bool(f(x) >= 0) * y, 1))

    Eq << Algebra.Gt_0.of.Ge.apply(Eq[0])

    Eq << Algebra.Or.of.Gt_0.split.Mul.apply(Eq[-1])

    Eq << Logic.And_And.of.And.apply(Eq[-1])

    Eq << Algebra.Cond.of.Gt_0.apply(Eq[-1])

    Eq << Algebra.Ge.of.Gt.strengthen.apply(Eq[-1])

    Eq << LessEqual(Eq[-1].lhs, 1, plausible=True)

    Eq << Algebra.Eq.of.Ge.Le.apply(Eq[-2], Eq[-1])

    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-11-05
