from util import *


@apply
def apply(le, contains, notcontains):
    y_, Y = contains.of(Element)
    S[y_], X = notcontains.of(NotElement)

    ((a, S[y_]), (((S[a], x), (S[x], S[X])), S[X])), ((S[a], S[y_]), (((S[a], y), (S[y], Y)), S[Y]))= le.of(Abs[Indexed - Sum[Indexed] / Card] <= Abs[Indexed - Sum[Indexed] / Card])

    X_ = X | {y_}
    Y_ = Y - {y_}
    return LessEqual(Sum[x:X_]((a[x] - (Sum[x:X_](a[x])) / (Card(X) + 1)) ** 2) + Sum[y:Y_]((a[y] - Sum[y:Y_](a[y]) / (Card(Y) - 1)) ** 2),
                     Sum[x:X]((a[x] - (Sum[x:X](a[x])) / Card(X)) ** 2) + Sum[y:Y]((a[y] - Sum[y:Y](a[y]) / Card(Y)) ** 2))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool, Nat

    y_quote = Symbol(integer=True, given=True)
    x, y = Symbol(integer=True)
    a = Symbol(real=True, shape=(oo,), given=True)
    X, Y = Symbol(etype=dtype.integer, finiteset=True, given=True)
    Eq << apply(abs(a[y_quote] - Sum[x:X](a[x]) / Card(X)) <= abs(a[y_quote] - Sum[y:Y](a[y]) / Card(Y)), Element(y_quote, Y), NotElement(y_quote, X))

    Eq.eq, Eq.ne = Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=Equal(Card(Y), 1))

    Eq.suffice_et = Bool.Imp_And.of.Cond.apply(Eq[1], cond=Eq.eq.lhs)

    Eq << Eq.suffice_et.this.rhs.apply(Set.Eq_Empty.of.Eq.In)

    Eq <<= Eq.eq & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Nat.Eq.UnaryFn.given.Eq.UnaryFn)

    Eq << Bool.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq.suffice_eq = Eq.suffice_et.this.rhs.apply(Set.EqFinset.of.Eq.In)

    Eq <<= Eq.suffice_eq & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Nat.Eq.UnaryFn.given.Eq.UnaryFn)

    Eq << Bool.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Le.given.Eq)

    Eq << Bool.Imp.of.Cond.apply(Eq[0], cond=Eq[-1].lhs)

    Eq <<= Eq[-1] & Eq.suffice_eq

    Eq << Eq[-1].this.rhs.apply(Bool.Cond.of.Eq.Cond.subst)

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq_0.of.Abs.le.Zero)

    Eq << Bool.Imp.of.Cond.apply(Eq[2], cond=Eq[-1].lhs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Set.EqSumS_SquareSub_DivSum__Card.of.Eq_DivSum__Card.NotIn)

    Eq << Set.EqCard.of.NotIn.apply(Eq[2])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Set.GeCard.of.In.apply(Eq[1])

    Eq << Bool.Imp_And.of.Cond.apply(Eq[-1], cond=Eq.ne.lhs)

    Eq << Eq[-1].this.rhs.apply(Nat.Ge_Add_1.of.Gt)

    Eq << Bool.Imp.of.Cond.apply(Eq[0] & Eq[1] & Eq[2], cond=Eq.ne.lhs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Set.LeAddSSumS_SquareSub_Sum.of.Le.Ge.In.NotIn)





if __name__ == '__main__':
    run()
# created on 2021-03-25
# updated on 2023-08-26
