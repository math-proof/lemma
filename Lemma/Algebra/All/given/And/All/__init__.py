from util import *


@apply
def apply(given, *, cond=None, wrt=None):
    from Lemma.Bool.All.All.of.All import split
    given = split(All, given, cond, wrt)
    if given.is_And:
        lhs, rhs = given.of(And)
        return lhs, rhs
    else:
        return given


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x = Symbol(real=True)
    d = Symbol(real=True, positive=True)
    f = Function(integer=True)
    Eq << apply(All[x:-d:d](f(x) > 0), cond=x > 0)

    Eq << Bool.AllOr.of.All.All.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()

# created on 2018-12-06

from . import split
