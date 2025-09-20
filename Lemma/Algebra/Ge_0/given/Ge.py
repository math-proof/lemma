from util import *


@apply
def apply(given):
    *x, y = given.of(Expr - Expr >= 0)
    x = Add(*x)
    return GreaterEqual(x, y)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, b = Symbol(real=True, given=True)
    Eq << apply(LessEqual(0, a - b))

    Eq << Algebra.Ge_0.of.Ge.apply(Eq[1]).reversed




if __name__ == '__main__':
    run()
# created on 2023-04-15
