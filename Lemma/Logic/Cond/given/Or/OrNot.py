from util import *


@apply
def apply(given, *, cond=None):
    assert cond.is_bool

    _eq = cond.invert()
    return Or(cond, given), Or(_eq, given)

@prove
def prove(Eq):
    e = Symbol(integer=True, given=True)
    f = Function(integer=True, shape=())
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq <<= Eq[1] & Eq[2]




if __name__ == '__main__':
    run()

# created on 2018-01-15
