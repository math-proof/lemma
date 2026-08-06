from util import *


@apply
def apply(given):
    n = given.of(Equal[Expr % 2, 0])
    return Equal(n // 2, (n + 1) // 2)


@prove
def prove(Eq):
    from Lemma import Nat, Int

    n = Symbol(integer=True)
    Eq << apply(Equal(n % 2, 0))

    Eq << Nat.OddAdd_1.of.Even.apply(Eq[0])

    Eq << Nat.Div_2.of.Odd.apply(Eq[-1])

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Int.FloorDiv_2.eq.Div_2.of.Even.apply(Eq[0])






if __name__ == '__main__':
    run()
# created on 2023-05-30
