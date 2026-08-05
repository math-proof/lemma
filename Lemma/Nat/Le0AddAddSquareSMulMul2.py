from util import *


@apply(simplify=False)
def apply(function):
    assert function.is_real
    square = function ** 2
    square = square.expand()
    return GreaterEqual(square, 0, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Nat

    x, y = Symbol(real=True)
    Eq << apply(x + y)

    Eq << ((x + y) ** 2).this.apply(Nat.SquareAdd.eq.AddAdd_SquareS_Mul2Add)

    Eq << Eq[0].subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()

# created on 2018-06-06
