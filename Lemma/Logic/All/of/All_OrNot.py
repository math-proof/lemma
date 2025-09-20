from util import *


@apply
def apply(given, pivot=0, wrt=None):
    [*conds] = given.of(Or)

    eq = conds.pop(pivot)

    if wrt is None:
        wrt = eq.wrt

    assert eq._has(wrt)

    cond = eq.invert()

    return All[wrt:cond](given.func(*conds))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    y = Symbol(complex=True, shape=(n,), given=True)
    f, g = Function(complex=True, shape=())
    Eq << apply(Unequal(f(x), g(y)) | Equal(x, y), pivot=1)

    Eq << ~Eq[-1]

    Eq << Logic.Any_And.of.AnySetOf.apply(Eq[-1])

    Eq << Logic.Any_And.of.Any.All.apply(Eq[0], Eq[-1])














if __name__ == '__main__':
    run()

# created on 2018-04-11
