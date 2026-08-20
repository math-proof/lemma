from util import *


@apply
def apply(given):
    (fx, (x, x0)), (epsilon, domain) = given.of(All[Limit > 0])
    S[0], delta = domain.of(Interval)
    assert delta > 0
    b = x0 + epsilon
    assert not b._has(epsilon)
    return GreaterEqual(Limit[x:b - S.Infinitesimal](fx), 0)


@prove(proved=False)
def prove(Eq):
    b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(real=True, continuous=Interval.open(-oo, b))
    epsilon, delta = Symbol(positive=True)
    Eq << apply(All[epsilon:Interval(0, delta, left_open=True)](Limit[x:b - epsilon](f(x)) > 0))
































if __name__ == '__main__':
    run()
# created on 2021-08-22
