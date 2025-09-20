from util import *


@apply
def apply(is_nonnegative, self, offset):
    expr = is_nonnegative.of(Expr >= 0)
    S[expr], (x, E) = self.of(Integral)
    E -= offset
    return Equal(self, Integral[x:E](expr._subs(x, x + offset)))


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra, Set

    x, a, b, d = Symbol(real=True)
    f = Function(real=True, integrable=True)
    Eq << apply(f(x) >= 0, Integral[x:Interval(a, b)](f(x)), d)

    Eq << Calculus.Integral.eq.Mul.Limit.Lebesgue.of.Ge_0.apply(Eq[0], Eq[1].lhs)

    Eq << Calculus.Integral.eq.Mul.Limit.Lebesgue.of.Ge_0.apply(Eq[0], Eq[1].rhs)

    Eq << Eq[-1].find(Sup).this.apply(Algebra.Sup.limits.subst.offset, -d)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Cup).apply(Set.CupIn_Ico.offset, -d)

    Eq << Eq[-1].this.find(Measure).apply(Set.Measure.offset)

    Eq << Eq[-1].subs(Eq[2].reversed).reversed


if __name__ == '__main__':
    run()
# created on 2020-05-22
