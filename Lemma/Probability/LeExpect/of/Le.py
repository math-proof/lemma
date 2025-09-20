from util import *


@apply
def apply(le, *limits):
    fx, gx = le.of(LessEqual)
    for v, *ab in limits:
        if v.is_random:
            fx = fx._subs(v.var, v)
            gx = gx._subs(v.var, v)

    return Expectation(fx, *limits) <= Expectation(gx, *limits)

@prove
def prove(Eq):
    from Lemma import Probability

    x = Symbol(real=True, random=True)
    f, g = Function(real=True)
    Eq << apply(f(x.var) <= g(x.var), (x,))

    Eq << Eq[0].reversed

    Eq << Probability.GeExpect.of.Ge.apply(Eq[-1], (x,))

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2023-04-04
