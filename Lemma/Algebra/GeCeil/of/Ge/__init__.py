from util import *


@apply
def apply(given):
    x, y = given.of(GreaterEqual)
    return GreaterEqual(Ceil(x), Ceil(y))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x >= y)

    Eq << Algebra.LeCeil.of.Le.apply(Eq[0].reversed).reversed




if __name__ == '__main__':
    run()
# created on 2021-12-27


# updated on 2022-01-04


from . import integer
