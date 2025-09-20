from util import *


@apply
def apply(given, *, cond=None):
    assert cond.is_bool
    return Or(given, cond)


@prove
def prove(Eq):
    e = Symbol(integer=True, given=True)
    f, g = Function(integer=True)
    Eq << apply(f(e) > 0, cond=g(e) > 0)

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2018-09-12
