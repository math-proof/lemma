from util import *


@apply
def apply(x, y, evaluate=False):
    assert x.is_real and y.is_real
    return LessEqual(Min(x, y), x, evaluate=evaluate)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True)
    Eq << apply(x, y)

    Eq << Algebra.Ge_Min.apply(x, y)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2023-04-23
from . import of
