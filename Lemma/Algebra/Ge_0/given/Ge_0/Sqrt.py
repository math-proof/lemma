from util import *


@apply
def apply(given):
    x = given.of(Expr >= 0)
    return sqrt(x) >= 0


@prove
def prove(Eq):
    from Lemma import Algebra, Int, Int, Int, Int

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    Eq << Int.Le0Mul.of.Ge_0.Ge_0.apply(Eq[1], Eq[1])




if __name__ == '__main__':
    run()
# created on 2023-06-20
