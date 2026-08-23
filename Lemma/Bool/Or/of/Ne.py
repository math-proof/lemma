from util import *


@apply(simplify=False)
def apply(given):
    x, y = given.of(Unequal)
    assert x.is_real and y.is_real
    return Or(x > y, x < y, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Nat

    x, y = Symbol(real=True, given=True)
    Eq << apply(Unequal(x, y))

    Eq << ~Eq[1]

    Eq << Eq[-1].this.apply(Nat.Eq.of.Le.Ge)

    Eq << ~Eq[-1]




if __name__ == '__main__':
    run()
# created on 2023-04-19

