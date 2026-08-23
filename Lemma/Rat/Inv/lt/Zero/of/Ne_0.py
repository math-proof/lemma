from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    assert x.is_nonpositive
    return Less(1 / x, 0, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Rat, Nat

    a = Symbol(real=True, nonpositive=True)
    Eq << apply(Unequal(a, 0))

    Eq << Nat.Lt_0.of.Ne_0.apply(Eq[0])

    Eq << Rat.Div.lt.Zero.of.Lt_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-22
