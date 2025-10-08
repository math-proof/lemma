from util import *


@apply
def apply(given):
    fx, fy = given.of(Imply)
    return Given(fy, fx)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Imply(f(n) < g(n), f(n + 1) < g(n + 1)))

    Eq << Bool.ImpNot.given.Or.apply(Eq[1])

    Eq << Bool.Or.of.ImpNot.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-03-04
