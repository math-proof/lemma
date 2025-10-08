from util import *


@apply(simplify=False)
def apply(given, index=0):
    eqs, fy = given.of(Imply)
    cond = eqs.of(And)
    cond = cond[index]
    if isinstance(index, slice):
        cond = And(*cond)

    return Imply(cond, fy)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    a, b, c = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Imply(Equal(a, 0) & Equal(b, 0), Equal(c, 0)), index=1)

    Eq << Bool.ImpAndS.of.Imp.apply(Eq[1], cond=Equal(a, 0))

    Eq << Bool.Imp.of.Imp_And.apply(Eq[-1], 1)


if __name__ == '__main__':
    run()
# created on 2018-10-12
