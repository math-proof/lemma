from util import *


@apply
def apply(given, old, new):
    from Lemma.Logic.Or_Not.of.All import rewrite_as_Or
    assert old in given.variables
    ou = rewrite_as_Or(given)
    return ou._subs(old, new)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    x, y = Symbol(integer=True)
    a = Symbol(integer=True, positive=True)

    f = Function(shape=(), integer=True)
    A, B = Symbol(etype=dtype.integer)

    Eq << apply(All[x:A, y:B](f(x, y) > 0), x, a)

    Eq << Logic.Or_Not.of.All.apply(Eq[0])

    Eq << Eq[-1].subs(x, a)
#


if __name__ == '__main__':
    run()

# created on 2018-06-19
