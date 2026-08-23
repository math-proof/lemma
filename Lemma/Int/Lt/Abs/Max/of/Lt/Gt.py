from util import *


@apply
def apply(lt, gt):
    x, a = lt.of(Less)
    S[x], b = gt.of(Greater)
    return Less(abs(x), Max(abs(a), abs(b)))


@prove
def prove(Eq):
    from Lemma import Nat, Set, Int

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(x < a, x > b)

    Eq << Int.Lt_Abs.given.And.apply(Eq[-1])

    Eq <<= ~Eq[-2], -~Eq[-1]

    Eq <<= Set.Ge.of.Ge.In_Iic.apply(Eq[-2], abs(a)), -Set.Ge.of.Ge.In_Iic.apply(Eq[-1], abs(b))

    Eq <<= Nat.Gt.of.Ge.Lt.apply(Eq[-2], Eq[0]), -Nat.Lt.of.Le.Lt.apply(Eq[1], Eq[-1])

    Eq <<= Int.GeAbs.apply(a), Int.GeAbs.apply(b, negate=True)

    Eq <<= Eq[-2] & Eq[-4], Eq[-1] & Eq[-3]


if __name__ == '__main__':
    run()
# created on 2019-12-19
# updated on 2023-04-17
