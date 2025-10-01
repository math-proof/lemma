from util import *


@apply
def apply(is_odd, contains_n):
    n = is_odd.of(Equal[Expr % 2, 1])
    S[n], ab = contains_n.of(Element)

    a, b = ab.of(Range)
    b -= 1

    return Element(n, imageset(n, 2 * n + 1, Range(a // 2, (b - 1) // 2 + 1)))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    a, b, n = Symbol(integer=True)
    Eq << apply(Equal(n % 2, 1), Element(n, Range(a, b + 1)))

    Eq << Algebra.Any.of.Eq_odd.apply(Eq[0])

    Eq << Logic.Any_And.of.Any.All.apply(Eq[1], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Logic.Cond.of.Eq.Cond.subst, ret=0)

    Eq << Eq[-1].this.find(Element).apply(Set.InSub.of.In_Icc, 1, simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Set.In.Div.Ico.of.In, 2, simplify=None)

    Eq << Eq[-1].this.find(Equal) - 1

    Eq << Eq[-1].this.find(Equal) / 2

    Eq << Eq[-1].this.rhs.args[0].apply(Algebra.Ceil.eq.FloorDivSub_Sign)

    S = Symbol(conditionset(n, Eq[-1]))
    Eq << S.this.definition

    Eq << Eq[-1].this.rhs.limits_subs(n, 2 * n + 1)

    Eq << Element(n, S, plausible=True)

    Eq << Eq[-1].this.rhs.definition

    Eq << Eq[-1].subs(Eq[-2])




if __name__ == '__main__':
    run()

# created on 2018-05-29
# updated on 2023-11-11
