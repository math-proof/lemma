from util import *


@apply
def apply(given):
    cond, S[0] = given.of(Unequal[Bool])
    return cond


@prove
def prove(Eq):
    from Lemma import Nat

    a, b = Symbol(real=True)
    Eq << apply(Unequal(Bool(a > b), 0))

    Eq << Nat.Ne.given.Gt.apply(Eq[0])

    Eq << Nat.Gt_0.given.Cond.apply(Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2023-11-05
# updated on 2025-04-20
