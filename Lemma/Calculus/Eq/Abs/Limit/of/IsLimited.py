from util import *


@apply
def apply(is_limited):
    from Lemma.Calculus.Any.All.of.IsLimited.limit_definition import of_limited
    fx, *limits = of_limited(is_limited, real=True)

    return Equal(Limit(abs(fx), *limits), abs(is_limited.lhs))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Calculus, Logic

    x, x0 = Symbol(real=True)
    g = Function(real=True)
    Eq << apply(Element(Limit[x:x0](g(x)), Reals))

    Eq << Set.Or.of.In_Icc.apply(Eq[0], 0)

    Eq << Eq[-1].this.args[1].apply(Set.Or.of.In_Icc, 0, left_open=True, simplify=None)

    Eq << Eq[-1].this.find(Element[FiniteSet]).apply(Set.Eq.of.In_Finset, simplify=None)

    Eq << Logic.Cond.given.And.Imp.apply(Eq[1], cond=Eq[-1], simplify=None)

    Eq << Logic.ImpOr.given.Imp.Imp.apply(Eq[-1], None)

    Eq << Logic.Imp.given.Imp.subst.apply(Eq[-3])

    Eq << Eq[-1].this.lhs.apply(Calculus.Eq_0.Limit.Abs.of.Eq_0)

    Eq <<= Eq[-2].this.lhs.apply(Set.EqAbs.of.IsNegative, ret=0), Eq[-3].this.lhs.apply(Set.EqAbs.of.IsPositive, ret=0)

    Eq <<= Logic.Imp_And.given.Imp.And.subst.apply(Eq[-2]), Logic.Imp_And.given.Imp.And.subst.apply(Eq[-1])

    Eq <<= Logic.Imp_And.given.Imp.delete.apply(Eq[-2], 0), Logic.Imp_And.given.Imp.delete.apply(Eq[-1], 0)

    Eq << Eq[-2].this.lhs.apply(Calculus.Eq.Limit.Abs.of.IsNegative)

    Eq << Eq[-1].this.lhs.apply(Calculus.Eq.Limit.Abs.of.IsPositive)





if __name__ == '__main__':
    run()
# created on 2023-04-18
# updated on 2023-05-13
