from util import *


@apply
def apply(given):
    fx, (x, S[1]) = given.of(Derivative > 0)
    domain = x.domain
    a, b = domain.of(Interval)
    assert not domain.left_open and domain.right_open
    return All[x:a:b](Greater(fx, fx._subs(x, a)))


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Bool

    a, b = Symbol(real=True)
    x = Symbol(domain=Interval(a, b, right_open=True))
    f = Function(real=True)
    Eq << apply(Derivative[x](f(x)) > 0)

    Eq << Bool.All.of.Cond.apply(Eq[0], x)

    Eq << Calculus.All.Gt.of.All_Gt_0.monotony.right_open.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-06-03
