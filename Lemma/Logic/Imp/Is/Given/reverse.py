from util import *


@apply
def apply(given):
    fx, fy = given.of(Imply)
    return Given(fy, fx)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Imply(f(n) < g(n), f(n + 1) < g(n + 1)))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Logic.Given.of.Imp.reverse)

    Eq << Eq[-1].this.rhs.apply(Logic.Imp.given.Given.reverse)


if __name__ == '__main__':
    run()
# created on 2019-10-07
