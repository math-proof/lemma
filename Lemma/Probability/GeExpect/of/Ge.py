from util import *


@apply
def apply(ge, *limits):
    fx, gx = ge.of(GreaterEqual)
    for v, *ab in limits:
        if v.is_random:
            fx = fx._subs(v.var, v)
            gx = gx._subs(v.var, v)
    return Expectation(fx, *limits) >= Expectation(gx, *limits)

@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Calculus

    x = Symbol(real=True, random=True)
    f, g = Function(real=True)
    Eq << apply(f(x.var) >= g(x.var), (x,))

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.eq.Integral)

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.eq.Integral)

    Eq << Probability.Pr.ge.Zero.apply(Eq[-1].find(Pr))

    Eq << Algebra.GeMul.of.Ge_0.Ge.apply(Eq[-1], Eq[0])

    Eq << Calculus.GeIntegral.of.Ge.apply(Eq[-1], (x.var,))




if __name__ == '__main__':
    run()
# created on 2023-04-04
