from util import *


@apply
def apply(self):
    fx, (x, s) = self.of(Cap)
    return Equal(self, fx.as_multiple_terms(x, s, cls=Cap))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f, g = Function(etype=dtype.real)
    Eq << apply(Cap[x:B](Piecewise((f(x, y), Element(x, A)), (g(x, y), True))))

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[0], wrt='y')

    Eq <<= Eq[-2].this.lhs.apply(Set.All_In.of.In_Cap), \
    Eq[-1].this.rhs.apply(Set.In_Cap.given.All_In)

    Eq <<= Eq[-2].this.lhs.expr.apply(Bool.OrAndS.of.BFn_Ite), \
    Eq[-1].this.rhs.expr.apply(Bool.BFn_Ite.given.OrAndS)

    Eq <<= Eq[-2].this.rhs.apply(Set.In_Inter.given.In.In, simplify=None), \
    Eq[-1].this.lhs.apply(Set.In.In.of.In_Inter, simplify=None)

    Eq <<= Eq[-2].this.rhs.find(Element).apply(Set.In_Cap.given.All_In), \
    Eq[-1].this.lhs.find(Element).apply(Set.All_In.of.In_Cap)

    Eq <<= Eq[-2].this.rhs.find(Element).apply(Set.In_Cap.given.All_In), \
    Eq[-1].this.lhs.find(Element).apply(Set.All_In.of.In_Cap)

    Eq <<= Eq[-2].this.lhs.apply(Bool.All.All.of.All, cond=A), Eq[-1].this.rhs.apply(Algebra.All.given.And.All.split, cond=A)

    Eq <<= Eq[-2].this.lhs.args[0].apply(Bool.All.Is.Imp), Eq[-1].this.rhs.args[0].apply(Bool.All.Is.Imp)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.apply(Set.In_Inter.Is.And_In_Inter, index=0, simplify=False), \
    Eq[-1].this.rhs.args[0].lhs.apply(Set.In_Inter.Is.And_In_Inter, index=0, simplify=False)

    Eq <<= Eq[-2].this.lhs.args[0].apply(Bool.Imp.subst.Bool, index=0, invert=True), \
    Eq[-1].this.rhs.args[0].apply(Bool.Imp.subst.Bool, index=0, invert=True)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.args[1].apply(Set.In_Inter.Is.And_In_Inter), \
    Eq[-1].this.rhs.args[0].lhs.args[1].apply(Set.In_Inter.Is.And_In_Inter)

    Eq <<= Eq[-2].this.lhs.args[0].apply(Bool.Imp.Is.All, wrt=x), \
    Eq[-1].this.rhs.args[0].apply(Bool.Imp.Is.All, wrt=x)

    Eq <<= Eq[-2].this.lhs.args[1].apply(Bool.All.Is.Imp), Eq[-1].this.rhs.apply(Bool.All.Is.Imp)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.apply(Set.In_SDiff.Is.And_NotIn), \
    Eq[-1].this.rhs.lhs.apply(Set.In_SDiff.Is.And_NotIn)

    Eq <<= Eq[-2].this.lhs.args[0].apply(Bool.Imp.subst.Bool, index=1, invert=True), \
    Eq[-1].this.rhs.apply(Bool.Imp.subst.Bool, index=1, invert=True)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.simplify(), Eq[-1].this.rhs.lhs.simplify()

    Eq <<= Eq[-2].this.lhs.args[0].apply(Bool.Imp.Is.All, wrt=x), \
    Eq[-1].this.rhs.apply(Bool.Imp.Is.All, wrt=x)




if __name__ == '__main__':
    run()

# created on 2021-01-26
# updated on 2023-04-29
