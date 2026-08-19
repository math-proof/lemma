from util import *


@apply
def apply(lt, given):
    a, b = lt.of(Less)
    (fx, (x, S[1])), (S[x], domain) = given.of(All[Derivative >= 0])
    S[a], S[b] = domain.of(Interval)
    assert domain.is_closed

    return All[x:Interval(a, b)](GreaterEqual(fx, fx._subs(x, a)))


@prove(proved=False)
def prove(Eq):
    a, b = Symbol(real=True, given=True)
    domain = Interval(a, b)
    x, t = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a < b, All[x:domain](Derivative[x](f(x)) >= 0))

    


if __name__ == '__main__':
    run()
# created on 2023-10-03
