from util import *


@apply
def apply(lt, is_finite):
    γ = lt.of(Abs < 1)
    fk, (k, *cond) = is_finite.of(Sup[Abs] < Infinity)
    if cond:
        S[0], S[oo] = cond
    assert k.is_integer
    return Element(Sum[k:oo](γ ** k * fk), Interval(-oo, oo))



@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    r = Symbol(shape=(oo,), real=True)
    γ = Symbol(real=True)
    k = Symbol(integer=True)
    Eq << apply(Abs(γ) < 1, Less(Sup[k:oo](Abs(r[k])), oo))

    Eq.gt_zero, Eq.le_zero = Logic.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=γ > 0)

    Eq.lt_zero, Eq.is_zero = Logic.Imp.given.And.Imp.split.apply(Eq.le_zero, cond=γ < 0)

    Eq << Logic.Imp.given.ImpEq.apply(Eq.is_zero)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Add.shift)

    Eq << Eq[-1].this.find(Sum)().expr.simplify()

    Eq << Logic.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq.gt_zero)

    Eq << Eq[-1].this.find(And[~Less]).apply(Algebra.Lt.of.LtAbs)

    Eq << Eq[-1].this.lhs.apply(Set.In.Icc.of.Lt.Gt)

    Eq << Logic.Cond.Imp.given.And.Imp.And.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Set.IsReal.Sum.of.In_Icc.IsFinite, simplify=None)

    Eq << Logic.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq.lt_zero)

    Eq << Eq[-1].this.find(Abs < 1).apply(Algebra.Gt.of.LtAbs)

    Eq << Eq[-1].this.lhs.apply(Set.In.Icc.of.Lt.Gt)

    Eq << Logic.Cond.Imp.given.And.Imp.And.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Set.IsReal.Sum.of.In_Icc.IsFinite.negative, simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-04-16
# updated on 2023-05-15
