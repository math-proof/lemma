from util import *


@apply
def apply(given):
    x, RR = given.of(Element)
    assert Element(0, RR) == False
    return Greater(abs(x), 0)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool, Int, Int, Int, Nat, Nat, Nat

    x = Symbol(complex=True)
    Eq << apply(Element(x, Reals - {0}))

    Eq << Set.OrInS.of.In_Union.apply(Eq[0], simplify=None)

    Eq.is_negative = Imply(Eq[-1].args[1], Eq[1], plausible=True)

    Eq << Eq.is_negative.this.lhs.apply(Set.Lt_0.of.IsNegative)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ne.of.Lt)

    Eq << Eq[-1].this.lhs.apply(Int.GtAbs_0.of.Ne_0)

    Eq.is_positive = Imply(Eq[2].args[0], Eq[1], plausible=True)

    Eq << Eq.is_positive.this.lhs.apply(Set.Gt_0.of.IsPositive)

    Eq << Eq[-1].this.lhs.apply(Nat.Ne.of.Gt)

    Eq << Bool.ImpOrS.of.Imp.Imp.apply(Eq.is_negative, Eq.is_positive)

    Eq << Bool.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])





if __name__ == '__main__':
    run()

# created on 2020-04-11
# updated on 2025-04-20
