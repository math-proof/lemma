from util import *


@apply(simplify=None)
def apply(given, d=1):
    x = given.of(Unequal[0])
    assert d > 0 or d < 0
    return Unequal(d / x, 0, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(real=True, given=True)
    Eq << apply(Unequal(x, 0))

    Eq << ~Eq[-1]

    Eq << Logic.Cond.of.Or_Not.Cond.apply(Eq[0], Eq[-1])

    Eq << Eq[-1] * x



if __name__ == '__main__':
    run()
# created on 2020-02-15
# updated on 2022-04-03
