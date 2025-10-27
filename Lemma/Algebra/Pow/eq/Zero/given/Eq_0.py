from util import *


@apply
def apply(given):
    x, n = given.of(Equal[Expr ** Expr, 0])
    assert n.is_integer and n > 0
    return Equal(x, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** n, 0))

    Eq << Nat.EqPowS.of.Eq.apply(Eq[1], exp=n)




if __name__ == '__main__':
    run()
# created on 2018-11-03
