from util import *


@apply
def apply(x, evaluate=False):
    return LessEqual(x, Ceil(x), evaluate=evaluate)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << Algebra.GeCeil.apply(x)
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2018-10-28
