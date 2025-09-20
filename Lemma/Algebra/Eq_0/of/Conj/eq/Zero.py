from util import *


@apply
def apply(given):
    x = given.of(Equal[Conjugate, 0])
    assert not x.is_set
    return Equal(x, 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(complex=True, given=True)
    Eq << apply(Equal(~x, 0))

    Eq << Algebra.EqConj.of.Eq.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2023-05-02
