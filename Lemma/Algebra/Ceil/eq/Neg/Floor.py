from util import *


@apply
def apply(ceil):
    x = ceil.of(Ceil)

    return Equal(ceil, -floor(-x))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    x = Symbol(real=True)
    Eq << apply(ceil(x))

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=Element(x, Integers))

    Eq << Eq[-2].this.lhs.apply(Set.Any.Eq.of.In)

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.EqCeil.of.Eq, ret=0)

    Eq << -Eq[-1].this.lhs.expr.args[0]

    Eq << Eq[-1].this.lhs.expr.args[0].apply(Algebra.EqFloor.of.Eq)

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.EqAdd.of.Eq.Eq)

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.given.Eq_0)

    Eq << Eq[2].this.lhs.apply(Set.EqCeil.of.IsNotInteger, ret=0)

    Eq << Eq[-1].this.find(NotElement).apply(Set.Eq.Floor.Frac.of.NotIn)

    Eq << Eq[-1].this.find(frac).apply(Algebra.Frac.eq.Sub_Floor)

    Eq << Eq[-1].this.lhs.apply(Algebra.EqAdd.of.Eq.Eq)




if __name__ == '__main__':
    run()
# created on 2018-05-21
# updated on 2023-05-14
