from util import *


@apply
def apply(equal, cond):
    b, x = equal.of(Equal)
    _x, a = cond.of(BinaryCondition)

    if x != _x:
        b, x = x, b

    assert x == _x

    return cond.func(b, a)


@prove
def prove(Eq):
    t, x, y = Symbol(real=True)

    Eq << apply(Equal(x, y), x >= t)

    Eq << Eq[-1].subs(Eq[0].reversed)


if __name__ == '__main__':
    run()
# created on 2020-10-01

from . import subs_with_expand_dims
