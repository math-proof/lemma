from util import *


@apply
def apply(given):
    x, d = given.of(Equal[Mod, 0])
    assert d.is_integer and d.is_nonzero
    return Equal(x, 0)


@prove
def prove(Eq):
    a, b = Symbol(integer=True)
    d = Symbol(integer=True, positive=True)
    Eq << apply(Equal((a - b) % d, 0))

    Eq << Eq[0].subs(Eq[1])


if __name__ == '__main__':
    run()
# created on 2021-07-28
