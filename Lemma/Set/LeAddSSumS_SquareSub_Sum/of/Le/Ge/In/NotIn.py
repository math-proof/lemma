from util import *


@apply
def apply(le, ge, contains, notcontains):
    ((a, y_), (((S[a], x), (S[x], X)), S[X])), ((S[a], S[y_]), (((S[a], y), (S[y], Y)), S[Y]))= le.of(Abs[Indexed - Sum[Indexed] / Card] <= Abs[Indexed - Sum[Indexed] / Card])
    S[Y] = ge.of(Card >= 2)
    S[y_], S[Y] = contains.of(Element)
    S[y_], S[X] = notcontains.of(NotElement)

    X_ = X | {y_}
    Y_ = Y - {y_}
    return LessEqual(Sum[x:X_]((a[x] - (Sum[x:X_](a[x])) / (Card(X) + 1)) ** 2) + Sum[y:Y_]((a[y] - Sum[y:Y_](a[y]) / (Card(Y) - 1)) ** 2),
                     Sum[x:X]((a[x] - (Sum[x:X](a[x])) / Card(X)) ** 2) + Sum[y:Y]((a[y] - Sum[y:Y](a[y]) / Card(Y)) ** 2))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    y_quote = Symbol(integer=True, given=True)
    x, y = Symbol(integer=True)
    t = Symbol(real=True, shape=(oo,), given=True)
    X, Y = Symbol(etype=dtype.integer, finiteset=True, given=True)
    Eq << apply(abs(t[y_quote] - Sum[x:X](t[x]) / Card(X)) <= abs(t[y_quote] - Sum[y:Y](t[y]) / Card(Y)), Card(Y) >= 2, Element(y_quote, Y), NotElement(y_quote, X))

    Eq << Algebra.Cond.of.Cond.domain_defined.apply(Eq[0])

    Eq << Logic.Cond.of.And.apply(Eq[-1], 0)

    a, b, a_quote, b_quote = Symbol(shape=(oo,), integer=True)
    Eq << Set.Any.Eq.of.Card.ne.Zero.apply(Eq[-1], a)

    Eq << Algebra.Gt_0.of.Ge.apply(Eq[1])

    Eq << Set.Any.Eq.of.Card.gt.Zero.apply(Eq[-1], b)



    Eq.Any_And = Algebra.Any.And.of.Any.Any.apply(Eq[-3], Eq[-1], simplify=None)
    Eq.abs_complement = Set.Eq.Card.SDiff.of.In.apply(Eq[2])
    Eq << Algebra.Ge.of.Eq.Ge.subst.apply(Eq.abs_complement, Eq[1])
    Eq << Algebra.Gt_0.of.Ge.apply(Eq[-1])
    Eq << Set.Any.Eq.of.Card.gt.Zero.apply(Eq[-1], b_quote)
    Eq << Eq[-1].subs(Eq.abs_complement)
    Eq.abs_union = Set.EqCard.of.NotIn.apply(Eq[3])
    Eq << Algebra.Gt_0.of.Eq.apply(Eq.abs_union)
    Eq << Set.Any.Eq.of.Card.gt.Zero.apply(Eq[-1], a_quote)
    Eq << Eq[-1].subs(Eq.abs_union)
    Eq << Algebra.Any.And.of.Any.Any.apply(Eq[-1], Eq[-4], simplify=None)
    Eq << Algebra.Any.And.of.Any.Any.apply(Eq.Any_And, Eq[-1], simplify=None)
    Eq << Logic.Any_And.of.Any.All.apply(Eq[0] & Eq[3], Eq[-1], simplify=None)
    Eq << Eq[-1].this.expr.apply(Set.Le.of.Eq_Cup.Eq_Cup.Eq_Cup.Eq_Cup.Le.NotIn)




if __name__ == '__main__':
    run()
# created on 2021-03-25
# updated on 2023-11-11

