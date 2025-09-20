from util import *


@apply
def apply(self):
    expr, (x, domain) = self.of(Integral)
    a, b = domain.of(Interval)
    return Equal(self, Integral[x:a:b](expr) * Bool(a <= b))


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra, Set, Logic

    x, a, b = Symbol(real=True)
    f = Function(real=True, continuous=True)
    Eq << apply(Integral[x:Interval(a, b)](f(x)))

    Eq << Eq[0].this.rhs.find(Integral).apply(Calculus.Integral.eq.Ite)

    Eq << Eq[-1].this.rhs.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Ite.eq.Ite_MulS)

    Eq << Logic.Cond_Ite.given.And.Imp.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Set.Icc.eq.Empty.of.Gt)

    Eq << Logic.Imp.given.Imp.subst.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-06-19
