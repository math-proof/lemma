from util import *


@apply
def apply(given, x=None, y=None):
    S = given.of(Equal[Card, 2])

    if x is None:
        x = S.generate_var(**S.etype.dict)
    if y is None:
        y = S.generate_var(excludes={x}, **S.etype.dict)
    return Any[x: Unequal(x, y), y](Equal(S, {x, y}))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool, Int, Int, Nat

    k = Symbol(integer=True, positive=True)
    S = Symbol(etype=dtype.integer[k])
    Eq << apply(Equal(Card(S), 2))

    Eq << Nat.Ge.of.Eq.apply(Eq[0])

    Eq << Set.Any.Ne.of.Ge.apply(Eq[-1], *Eq[1].variables)

    Eq << Set.Any.of.Any.limits.swap.apply(Eq[-1], simplify=False)

    Eq.S_supset = Eq[-1].this.expr.apply(Set.Subset.Finset.of.In.In, simplify=False)

    Eq << Eq.S_supset.this.expr.apply(Set.EqUnion.of.Subset, simplify=None, ret=0)

    Eq << Bool.AnySetOf.of.Any_And.apply(Eq[-1], index=1)

    Eq << Eq[-1].this.expr.apply(Set.EqCard.of.Eq)

    Eq << Eq[-1].this.find(Card).apply(Set.Card.eq.Add)


    Eq << Eq[-1].this.find(Piecewise).apply(Int.Ite.eq.AddMulS)
    Eq << Eq[-1].subs(Eq[0])
    Eq << Eq[-1].this.expr - 2
    Eq << Eq[-1].this.expr.apply(Int.Eq.of.Sub.eq.Zero)
    Eq << Any(Unequal(Eq[-1].rhs, 0), *Eq.S_supset.limits, plausible=True)
    Eq << Eq[-1].this.expr.apply(Algebra.EqDelta.of.Ne_0)
    Eq << Bool.Any_And.of.AnySetOf_AnySetOf.apply(Eq[-1])
    Eq << ~Eq[-2]
    Eq << Bool.Any_And.of.Any.All.All_Imp.apply(Eq[-1], Eq[-4])
    Eq << Eq[-1].this.expr.apply(Bool.Eq.of.Eq.Eq)
    Eq << Eq[-1].this.expr.apply(Set.Subset.of.Eq_0)
    Eq << Bool.Any_And.of.AnySetOf_AnySetOf.apply(Eq[-1])
    Eq << Bool.AnySetOf.of.Any_And.apply(Eq[-1])
    Eq << Eq[-1].this.expr.apply(Set.Eq.of.Subset.Subset.squeeze)




if __name__ == '__main__':
    run()

# created on 2020-09-07
# updated on 2023-06-01
