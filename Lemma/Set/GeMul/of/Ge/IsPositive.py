from util import *


@apply
def apply(lt, is_positive):
    x, R = is_positive.of(Element)
    assert R in Interval.open(0, oo)
    lhs, rhs = lt.of(GreaterEqual)
    return GreaterEqual(lhs * x, rhs * x)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    a, b = Symbol(real=True)
    x = Symbol(hyper_real=True)
    Eq << apply(a >= b, Element(x, Interval.open(0, oo)))

    Eq << Set.Any.Eq.of.In.apply(Eq[1])

    Eq << Bool.Any_And.of.AnySetOf_AnySetOf.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).simplify()

    Eq << Bool.Any_And.of.Any.All.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[1:].apply(Algebra.GeMul.of.Gt_0.Ge)

    Eq << Eq[-1].this.expr.apply(Bool.Cond.of.Eq.Cond.subst, reverse=True)




if __name__ == '__main__':
    run()
# created on 2021-10-02
# updated on 2023-05-14
