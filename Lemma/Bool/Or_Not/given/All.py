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
    from Lemma import Algebra, Bool
    n = Symbol(integer=True, positive=True)
    x, y = Symbol(complex=True, shape=(n,))

    f, g = Function(complex=True, shape=())

    Eq << apply(Unequal(f(x), g(y)) | Equal(x, y), pivot=1)

    Eq << Bool.Or_Not.of.All.apply(Eq[1])


if __name__ == '__main__':
    run()

# created on 2018-12-02
