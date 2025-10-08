from util import *


@apply
def apply(cond, suffice):
    p, q = suffice.of(Imply)
    return Imply(p & cond, q)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    x, y, a, b = Symbol(integer=True, given=True)


    f, g = Function(real=True)

    Eq << apply(a > b, Imply(x > y, f(x) > g(y)))

    Eq << Bool.Imp.given.Or_Not.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << Bool.BFn.of.BFnIte.Cond.apply(Eq[0], Eq[-1])

    Eq << Bool.Or.of.ImpNot.apply(Eq[1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-03-22
