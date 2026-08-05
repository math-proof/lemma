from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    if x is None: 
        x = given.of(Expr > 0)
    return Unequal(sqrt(x), 0)


@prove
def prove(Eq):
    from Lemma import Nat

    x = Symbol(real=True, given=True)
    Eq << apply(x > 0)

    Eq << ~Eq[-1]
    Eq.ne_0 = Nat.Ne.of.Gt.apply(Eq[0])

    Eq << Nat.Pow.of.Eq.apply(Eq[-1], exp=2)
    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-07-16
