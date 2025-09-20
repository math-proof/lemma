from util import *


@apply
def apply(self):
    expr, (x, ss) = self.of(Cup[FiniteSet, Tuple[Intersection]])
    return Subset(self, Intersection(*(imageset(x, expr, s) for s in ss)))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    n, m = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    f = Function(complex=True, shape=(m,))
    A, B = Symbol(etype=dtype.complex[n])
    Eq << apply(imageset(x, f(x), A & B))

    y = Symbol(complex=True, shape=(m,))
    S = Symbol(Eq[0].lhs)
    S_quote = Symbol("S'", Eq[0].rhs)
    Eq.suffice = Imply(Element(y, S), Element(y, S_quote), plausible=True)

    Eq << Eq.suffice.this.lhs.rhs.definition

    Eq << Eq[-1].this.rhs.rhs.definition

    Eq << Eq[-1].this.rhs.apply(Set.In_Inter.given.And, simplify=False)

    Eq << Eq[-1].apply(Logic.Imp_And.given.Imp.Imp)

    Eq << Logic.And_And.given.And.Cond.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.rhs.apply(Set.Cup.eq.UnionCupS, cond=B), Eq[-1].this.rhs.rhs.apply(Set.Cup.eq.UnionCupS, cond=A)

    Eq <<= Eq[-2].this.rhs.apply(Set.In_Union.given.OrInS, simplify=False), Eq[-1].this.rhs.apply(Set.In_Union.given.OrInS, simplify=False)

    Eq << Set.Subset.of.Imp.apply(Eq.suffice)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition


if __name__ == '__main__':
    run()

# created on 2021-04-26
