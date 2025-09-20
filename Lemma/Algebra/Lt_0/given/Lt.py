from util import *


@apply
def apply(given):
    x, y = given.of(Expr - Expr < 0)
    return Less(x, y)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, b = Symbol(real=True, given=True)
    Eq << apply(Greater(0, a - b))

    Eq << Algebra.Lt_0.of.Lt.apply(Eq[-1]).reversed




if __name__ == '__main__':
    run()
# created on 2023-04-15
