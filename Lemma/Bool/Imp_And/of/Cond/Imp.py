from util import *


@apply
def apply(cond, suffice):
    p, q = suffice.of(Imply)
    return Imply(p, q & cond)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y, a, b = Symbol(integer=True)
    f, g = Function(real=True)
    Eq << apply(a > b, Imply(x > y, f(x) > g(y)))

    Eq << Bool.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Bool.Imp.given.Or_Not.apply(Eq[-1])

    Eq << Bool.Or.of.Cond.apply(Eq[0], cond=x <= y)


if __name__ == '__main__':
    run()
# created on 2018-09-12
