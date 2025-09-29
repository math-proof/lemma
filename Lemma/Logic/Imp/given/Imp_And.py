from util import *


@apply(simplify=False)
def apply(given):
    cond, fy = given.of(Imply)
    return Imply(cond, cond & fy)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    a, b, c = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Imply(Equal(a, 0), Equal(c, 0)))

    Eq << Logic.Imp.of.Imp_And.apply(Eq[1], index=1)


if __name__ == '__main__':
    run()
# created on 2018-06-10
