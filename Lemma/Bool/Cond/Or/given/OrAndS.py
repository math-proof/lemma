from util import *


@apply
def apply(cond, ou):
    if not ou.is_Or:
        cond, ou = ou, cond
    args = ou.of(Or)

    return Or(*((arg & cond).simplify() for arg in args))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    a, b, c, d = Symbol(integer=True, given=True)
    x, y = Symbol(real=True, given=True)
    f, g = Function(real=True)
    Eq << apply(f(x) < g(y), (a < b) | (c < d))

    Eq << Bool.And_Or.of.OrAndS.apply(Eq[-1], cond=f(x) < g(y))


if __name__ == '__main__':
    run()
# created on 2018-01-14
