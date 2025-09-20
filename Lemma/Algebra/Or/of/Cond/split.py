from util import *


@apply
def apply(given, *, cond=None):
    assert cond.is_bool
    return Or(given & cond.invert(), cond)


@prove
def prove(Eq):
    e = Symbol(integer=True, given=True)
    f, g = Function(integer=True, shape=())
    Eq << apply(f(e) > 0, cond=g(e) > 0)

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2021-08-08
