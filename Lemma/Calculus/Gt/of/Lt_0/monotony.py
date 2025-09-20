from util import *


@apply
def apply(given):
    fx, (x, S[1]) = given.of(Derivative < 0)
    domain = x.domain

    assert domain.right_open
    a, b = domain.of(Interval)
    return Greater(fx, fx._subs(x, b))


@prove(proved=False)
def prove(Eq):
    a, b = Symbol(real=True)

    x = Symbol(domain=Interval(a, b, right_open=True))

    f = Function(real=True)

    Eq << apply(Derivative[x](f(x)) < 0)


if __name__ == '__main__':
    run()

# created on 2020-10-16
