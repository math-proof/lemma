from util import *


@apply
def apply(self):
    fx, (x, s) = self.of(Cup)
    return Equal(self, fx.as_multiple_terms(x, s, cls=Cup))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f, g = Function(etype=dtype.real)
    Eq << apply(Cup[x:B](Piecewise((f(x, y), Element(x, A)), (g(x, y), True))))

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[0], wrt='y')

    Eq <<= Eq[-2].this.lhs.apply(Set.Any_In.of.In_Cup), \
    Eq[-1].this.rhs.apply(Set.In_Cup.given.Any_In)

    Eq <<= Eq[-2].this.lhs.expr.apply(Bool.OrAndS.of.BFn_Ite), \
    Eq[-1].this.rhs.expr.apply(Bool.BFn_Ite.given.OrAndS)

    Eq <<= Eq[-2].this.lhs.apply(Bool.OrAnyS.of.Any_Or), \
    Eq[-1].this.rhs.apply(Bool.Any_Or.given.OrAnyS)

    Eq <<= Eq[-2].this.lhs.args[0].apply(Bool.AnySetOf.of.Any_And, index=0), \
    Eq[-1].this.rhs.args[0].apply(Bool.Any_And.given.AnyAnd, index=0)

    Eq <<= Eq[-2].this.lhs.args[1].apply(Bool.AnySetOf.of.Any_And, index=1), \
    Eq[-1].this.rhs.args[1].apply(Bool.Any_And.given.AnyAnd, index=1)

    Eq <<= Eq[-2].this.rhs.apply(Set.In_Union.given.OrInS, simplify=None), \
    Eq[-1].this.lhs.apply(Set.OrInS.of.In_Union, simplify=None)

    Eq <<= Eq[-2].this.rhs.find(Element).apply(Set.In_Cup.given.Any_In), \
    Eq[-1].this.lhs.find(Element).apply(Set.Any_In.of.In_Cup)

    Eq << Eq[-2].this.rhs.find(Element).apply(Set.In_Cup.given.Any_In)

    Eq << Eq[-1].this.lhs.find(Element).apply(Set.Any_In.of.In_Cup)





if __name__ == '__main__':
    run()

# created on 2018-10-03
# updated on 2023-05-20
from . import double
