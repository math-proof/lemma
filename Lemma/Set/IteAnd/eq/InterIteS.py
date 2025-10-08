from util import *


@apply
def apply(self):
    (s, et), (emptySet, S[True]) = self.of(Piecewise)
    assert not emptySet

    eqs = et.of(And)
    return Equal(self, Intersection(*(Piecewise((s, eq), (emptySet, True)) for eq in eqs)))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    n = Symbol(integer=True, positive=True)
    s = Function(etype=dtype.complex[n])
    x, t = Symbol(complex=True, shape=(n,))
    f, g = Function(integer=True, shape=())
    Eq << apply(Piecewise((s(x), (f(x) > 0) & (g(x) > 0)), (x.emptySet, True)))

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[0], wrt=t)

    Eq <<= Eq[-2].this.find(Element).apply(Bool.OrAndS.of.BFn_Ite), \
    Eq[-1].this.find(Element).apply(Set.In.In.of.In_Inter)

    Eq <<= Eq[-2].this.rhs.apply(Set.In_Inter.given.In.In, simplify=False), \
    Eq[-1].this.lhs.find(Element).apply(Bool.OrAndS.of.BFn_Ite)

    Eq <<= Eq[-2].this.rhs.find(Element).apply(Bool.BFn_Ite.given.OrAndS), \
    Eq[-1].this.lhs.find(Element).apply(Bool.OrAndS.of.BFn_Ite)

    Eq << Eq[-2].this.rhs.apply(Bool.BFn_Ite.given.OrAndS)

    Eq << Eq[-1].this.rhs.apply(Bool.BFn_Ite.given.OrAndS)




if __name__ == '__main__':
    run()

# created on 2018-09-25
# updated on 2023-04-29
