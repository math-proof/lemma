from util import *


@apply
def apply(given):
    x, e = given.of(Equal)
    assert e.is_real
    return Element(x, Reals)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(super_complex=True)
    e = Symbol(real=True)
    Eq << apply(Equal(x, e))

    Eq << Algebra.Any.of.Cond.apply(Eq[0], e)


if __name__ == '__main__':
    run()
# created on 2020-05-03
