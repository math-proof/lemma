from util import *


@apply(simplify=False)
def apply(cond, suffice):
    lhs, fy = suffice.of(Imply)
    return cond, Imply(cond & lhs, fy)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    a, b, c = Symbol(integer=True)
    Eq << apply(Equal(b, 0), Imply(Equal(a, 0), Equal(c, 0)))

    Eq << Logic.BFn.of.BFnIte.Cond.apply(Eq[0], Eq[2])





if __name__ == '__main__':
    run()
# created on 2019-08-15
# updated on 2023-06-22
