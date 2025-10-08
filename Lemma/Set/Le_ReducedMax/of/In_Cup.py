from util import *


@apply
def apply(self):
    c, (xi, (i, S[0], n)) = self.of(Element[Cup[FiniteSet]])
    return c <= ReducedMax(Stack[i:n](xi).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    c = Symbol(real=True)
    Eq << apply(Element(c, x[:n].cup_finiteset()))

    Eq << Eq[1].this.rhs.apply(Algebra.ReducedMax.eq.Maxima)

    Eq << Algebra.All_Le_Maxima.apply(Eq[-1].rhs)

    Eq << Set.Any_In.of.In_Cup.apply(Eq[0])

    Eq << Bool.Any_And.of.Any.All.All_Imp.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.expr.apply(Algebra.Le.of.Eq.Le)


if __name__ == '__main__':
    run()
# created on 2023-11-12
