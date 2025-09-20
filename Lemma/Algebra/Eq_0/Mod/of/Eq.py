from util import *


@apply
def apply(given, d, swap=False):
    x, y = given.of(Equal)
    assert x.is_integer or y.is_integer
    d = sympify(d)
    assert d.is_integer and d.is_nonzero
    if swap:
        x, y = y, x
    return Equal((x - y) % d, 0)


@prove
def prove(Eq):
    a, b = Symbol(integer=True)
    d = Symbol(integer=True, positive=True)
    Eq << apply(Equal(a, b), d)

    Eq << Eq[1].subs(Eq[0])

    


if __name__ == '__main__':
    run()
# created on 2018-11-23
# updated on 2023-05-22
