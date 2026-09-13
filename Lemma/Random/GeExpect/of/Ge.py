from util import *


@apply
def apply(ge, *limits):
    fx, gx = ge.of(GreaterEqual)
    for v, *ab in limits:
        if v.is_random:
            fx = fx._subs(v.bvar, v)
            gx = gx._subs(v.bvar, v)
    return Expectation(fx, *limits) >= Expectation(gx, *limits)

@prove
def prove(Eq):
    from Lemma import Random, Real, Nat

    x = Symbol(real=True, random=True)
    f, g = Function(real=True)
    Eq << apply(f(x.bvar) >= g(x.bvar), (x,))

    Eq << Eq[-1].this.lhs.apply(Random.Expect.eq.Integral)

    Eq << Eq[-1].this.rhs.apply(Random.Expect.eq.Integral)

    Eq << Random.Prob.ge.Zero.apply(Eq[-1].find(Pr))

    Eq << Nat.GeMul.of.Ge_0.Ge.apply(Eq[-1], Eq[0])

    Eq << Real.GeIntegral.of.Ge.apply(Eq[-1], (x.bvar,))




if __name__ == '__main__':
    run()
# created on 2023-04-04
