from util import *


@apply
def apply(given):
    x, y = given.of(Mul >= 0)
    return x >= 0, y >= 0


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x * y >= 0)

    Eq << Algebra.Ge_0.of.Ge_0.Ge_0.apply(*Eq[1:])



if __name__ == '__main__':
    run()
# created on 2023-04-15
