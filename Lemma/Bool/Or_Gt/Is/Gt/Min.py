from util import *


@apply
def apply(given):
    (x, a), (S[x], b) = given.of(Greater | Greater)
    return Greater(x, Min(a, b))


@prove
def prove(Eq):
    from Lemma import Bool, Nat

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(Greater(x, a) | Greater(x, b))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(Bool.Or.Gt.of.Gt_Min)

    Eq << Eq[-2].this.rhs.apply(Nat.Gt_Min.given.Or.Gt)


if __name__ == '__main__':
    run()
# created on 2022-01-02
