from util import *


@apply
def apply(given):
    fx, fy = given.of(Given)
    return Imply(fy, fx)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Given(f(n) < g(n), f(n + 1) < g(n + 1)))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Bool.Imp.of.Given.reverse)

    Eq << Eq[-1].this.rhs.apply(Bool.Given.given.Imp.reverse)


if __name__ == '__main__':
    run()
# created on 2019-03-05
