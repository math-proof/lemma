from util import *


@apply
def apply(given, *, cond=None):
    p, q = given.of(Imply)
    return And(Imply(p & cond, q), Imply(p & cond.invert(), q))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    f, g = Function(integer=True)
    x, y = Symbol(integer=True)
    Eq << apply(Imply(Equal(f(x), f(y)), Equal(g(x), g(y))), cond=x > 0)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Logic.And.Imp.of.Imp.split, cond=Eq[0].find(Greater))

    Eq << Eq[-1].this.rhs.apply(Logic.Imp.given.And.Imp.split, cond=Eq[0].find(Greater))


if __name__ == '__main__':
    run()
# created on 2023-04-25
