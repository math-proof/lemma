from util import *


@apply
def apply(ge, ge1):
    b, x = ge.of(GreaterEqual)
    _x, a = ge1.of(GreaterEqual)
    if b == a:
        b, x, _x, a = _x, a, b, x
    assert x == _x
    return GreaterEqual(b, a)


@prove
def prove(Eq):
    x, a, b = Symbol(real=True)

    Eq << apply(b >= x, x >= a)

    Eq << Eq[0] + Eq[1]

    Eq << Eq[-1] - x


if __name__ == '__main__':
    run()
# created on 2018-03-12

