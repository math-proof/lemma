from util import *


@apply
def apply(ceil):
    x = ceil.of(Ceil)

    return Equal(ceil, -floor(-x))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool, Rat, Int

    x = Symbol(real=True)
    Eq << apply(ceil(x))

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=Element(x, Integers))

    Eq << Eq[-2].this.lhs.apply(Set.Any_Eq.of.In)

    Eq << Eq[-1].this.lhs.expr.apply(Rat.Ceil.of.Eq, ret=0)

    Eq << -Eq[-1].this.lhs.expr.args[0]

    Eq << Eq[-1].this.lhs.expr.args[0].apply(Rat.Floor.of.Eq)

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.EqAdd.of.Eq.Eq)

    Eq << Eq[-1].this.rhs.apply(Int.Eq.given.Sub.eq.Zero)

    Eq << Eq[2].this.lhs.apply(Set.Ceil.eq.AddFloor_1.of.NotIn_Range, ret=0)

    Eq << Eq[-1].this.find(NotElement).apply(Set.FloorNegFrac.eq.Neg1.of.NotIn_Range)

    Eq << Eq[-1].this.find(frac).apply(Rat.Frac.eq.Sub_Floor)

    Eq << Eq[-1].this.lhs.apply(Algebra.EqAdd.of.Eq.Eq)




if __name__ == '__main__':
    run()
# created on 2018-05-21
# updated on 2023-05-14
