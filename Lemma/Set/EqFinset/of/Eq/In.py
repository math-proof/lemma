from util import *


@apply
def apply(equal, contains):
    a, A = contains.of(Element)
    S[A] = equal.of(Equal[Card, 1])
    return Equal(A, a.set, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    A = Symbol(etype=dtype.integer, given=True)
    a = Symbol(integer=True, given=True)
    Eq << apply(Equal(Card(A), 1), Element(a, A))

    Eq << Set.Any.Eq.One.of.Eq.apply(Eq[0], reverse=True)

    Eq << Bool.Any_And.of.Any.All.apply(Eq[1], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Bool.Cond.of.Eq.Cond.subst, ret=0)

    Eq << Eq[-1].this.expr.apply(Bool.UFn.of.UFn.Eq, reverse=True)




if __name__ == '__main__':
    run()
# created on 2021-03-15
# updated on 2023-05-20
