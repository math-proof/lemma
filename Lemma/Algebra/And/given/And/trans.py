from util import *

from Lemma.Logic.Eq.of.Eq.Eq import transit


@apply
def apply(imply, swap=False, reverse=False):
    ab, bc = imply.of(And)
    if swap:
        ab, bc = bc, ab
    ac = transit(ab, bc, reverse=reverse)
    return ab, ac


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    x, i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a, b, c = Symbol(integer=True, shape=(oo,))

    S = Symbol(etype=dtype.integer)

    Eq << apply(Equal(a[i], b[i]) & Equal(b[i], c[i]))

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[1], Eq[2])

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

# created on 2019-05-04
