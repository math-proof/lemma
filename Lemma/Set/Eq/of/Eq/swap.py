from util import *


@apply
def apply(given, i=None, j=None):
    from Lemma.Set.EqSwapSwap import swap
    x, y = given.of(Equal)
    n, = x.shape

    assert x.dtype.is_set
    if i is None:
        i = Symbol(integer=True)

    if j is None:
        j = Symbol(integer=True)

    return Equal(swap[i, j](x), swap[i, j](y))


@prove
def prove(Eq):
    n = Symbol(positive=True, integer=True)

    x, y = Symbol(shape=(n,), etype=dtype.integer)

    Eq << apply(Equal(x, y))

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2021-03-29
