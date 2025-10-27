from util import *


@apply
def apply(given):
    x = given.of(Equal[Expr ** 2, 0])
    assert x.is_extended_real
    return Equal(x, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat, Int

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(x ** 2, 0))

    Eq << Nat.EqPowS.of.Eq.apply(Eq[0], exp=S.One / 2)

    Eq << Int.Eq_0.of.EqAbs_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-03-16

