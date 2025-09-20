from util import *


@apply
def apply(given, *vars):
    S, positive = given.of(Card >= Expr)
    assert positive > 1

    if vars:
        x, y = vars
    else:
        x = S.element_symbol()
        y = S.element_symbol({x})

    return Any[x:S, y:S](Unequal(x, y))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    S = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Card(S) >= 2)

    Eq << Set.Any_In.of.Ge.apply(Eq[0], simplify=False)

    Eq << Set.Any_In.of.Any_In.limits_restricted.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.expr.apply(Set.EqUnion.of.In)

    i = Eq[-1].variable
    Eq << Eq[-1].this.expr.apply(Set.EqCard.of.Eq)

    Eq << Eq[-1].this.find(Card).apply(Set.Card.eq.Add)



    Eq << Eq[-1].this.expr - 1

    Eq << Eq[0] - 1

    Eq << Algebra.Any.of.Any_Eq.Cond.subst.apply(Eq[-2].reversed, Eq[-1])

    Eq << Eq[-1].this.expr.apply(Set.Ne_Empty.of.Ge, simplify=False)

    i, j = Eq[1].variables
    Eq << Any[i:S, j:S](Element(j, Eq[-1].lhs), plausible=True)

    Eq << Eq[-1].simplify()

    Eq << ~Eq[1]

    Eq << Algebra.Any.of.All_Eq.Any.subst.apply(Eq[-1], Eq[-2])




if __name__ == '__main__':
    run()

# created on 2020-07-15
# updated on 2023-06-01
