from util import *


@apply
def apply(given, epsilon=None, delta=None, upper=1):
    from Lemma.Calculus.Eq.Is.Any_All.limit_definition import Any_All
    upper = sympify(upper)
    return Any_All(given, epsilon, delta, upper)


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Logic

    x, a = Symbol(real=True)
    x = Symbol(integer=True)
    f = Function(real=True, shape=())
    Eq << apply(Equal(Limit[x:oo](f(x)), a))

    Eq.all = Logic.All.of.Cond.apply(Eq[1], Eq[1].find(Abs < ~Symbol))

    ε = Eq.all.variable
    Eq << All(Eq.all.expr, (ε, Interval(1, oo)), plausible=True)

    Eq << Algebra.All.given.And.All.split.apply(Eq[-1], cond=ε > 1)

    Eq << Algebra.Cond.of.All.subst.apply(Eq.all, ε, S.One / 2)

    Eq << Eq[-1].this.find(Less).apply(Algebra.Lt.of.Lt.relax, 1)

    χ = Symbol(domain=Interval.open(1, oo))
    Eq << Algebra.Cond.of.All.subst.apply(Eq.all, ε, 1 / χ)

    Eq << Eq[-1].this.find(Less).apply(Algebra.Lt.of.Lt.relax, χ)

    Eq << Logic.All.of.Cond.apply(Eq[-1], χ)

    Eq <<= Eq.all & Eq[2]

    Eq << Calculus.Eq_Limit.given.Any_All.limit_definition.apply(Eq[0])

    Eq << Algebra.Cond.given.All.apply(Eq[-1], Eq[-1].find(Abs < ~Symbol))




if __name__ == '__main__':
    run()
# created on 2023-04-17
