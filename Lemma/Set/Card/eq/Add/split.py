from util import *


@apply
def apply(self, A):
    B = self.of(Card)

    return Equal(self, Card(B - A) + Card(A & B))


@prove
def prove(Eq):
    from Lemma import Set

    A = Symbol(etype=dtype.integer)
    B = Symbol(etype=dtype.integer)
    Eq << apply(Card(B), A)

    C = Symbol(B - A)
    D = Symbol(B & A)
    Eq.C_def = C.this.definition

    Eq.D_def = D.this.definition

    Eq << Set.EqUnionS.of.Eq.Eq.apply(Eq.C_def, Eq.D_def)

    Eq << Set.EqCard.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Set.Card.eq.Add)

    Eq << Eq[-1].subs(Eq.C_def, Eq.D_def).reversed












if __name__ == '__main__':
    run()
# created on 2023-06-01
