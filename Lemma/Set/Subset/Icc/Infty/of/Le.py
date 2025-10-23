from util import *


@apply
def apply(given, left_open=False):
    a, b = given.of(LessEqual)
    return Subset(Interval(b, oo, left_open=left_open), Interval(a, oo, left_open=left_open))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool, Nat

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    t = Symbol(real=True)
    Eq << Set.Subset.given.All_In.apply(Eq[1], t)

    Eq << Eq[-1].this.expr.simplify()

    Eq << ~Eq[-1]

    Eq << Bool.Any_And.of.AnySetOf_AnySetOf.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).simplify()

    Eq << Eq[-1].this.expr.apply(Nat.Gt.of.Ge.Lt)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2021-02-26
