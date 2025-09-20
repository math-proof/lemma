from util import *


@apply
def apply(given):
    fx, fy = given.of(Given)
    return Imply(fy, fx)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Given(f(n) < g(n), f(n + 1) < g(n + 1)))

    Eq << Logic.Given.of.Imp.reverse.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2019-03-04
