from util import *


@apply
def apply(given):
    x, b = given.of(Equal)
    assert x <= b
    return GreaterEqual(x, b)


@prove
def prove(Eq):
    from Lemma import Algebra

    a = Symbol(integer=True)
    b = Symbol(integer=True, given=True)
    x = Symbol(domain=Range(a, b + 1), given=True)
    Eq << apply(Equal(x, b))

    Eq << Algebra.Eq.of.Ge.squeeze.apply(Eq[1])





if __name__ == '__main__':
    run()
# created on 2019-03-31
# updated on 2023-11-11

