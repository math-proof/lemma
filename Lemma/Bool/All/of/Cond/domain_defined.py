from util import *


@apply(simplify=False)
def apply(given, wrt=None):
    if wrt is None:
        wrt = given.wrt

    assert not wrt.is_given
    domain = given.domain_defined(wrt)

    return All[wrt:domain](given)


@prove
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(log(x) >= 1 - 1 / x)

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()
# created on 2020-05-29
