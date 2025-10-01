from util import *


@apply
def apply(greater_than, _greater_than):
    x, a = greater_than.of(LessEqual)
    y, b = _greater_than.of(GreaterEqual)

    assert x.is_integer and y.is_integer and a.is_integer and b.is_integer
    return Subset(Range(y, x + 1), Range(b, a + 1))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    a, b, x, y = Symbol(integer=True, given=True)
    Eq << apply(y <= b, x >= a)

    Eq << Set.Subset.given.All_In.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(Set.Or.of.NotIn_Ico)

    Eq << Logic.Any_And.of.AnySetOf.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Set.Ge.Le_Sub_1.of.In_Ico)

    # if self implies a False proposition, then self must be False
    Eq << Eq[-1].this.expr.apply(Algebra.Cond.Cond.Or.given.Or, simplify=False)

    Eq.any_ax, Eq.any_by = Any(Eq[-1].expr.args[0], *Eq[-1].limits, plausible=True), Any(Eq[-1].expr.args[1], *Eq[-1].limits, plausible=True)

    Eq <<= Logic.AnySetOf.of.Any_And.apply(Eq.any_ax, index=1), Logic.AnySetOf.of.Any_And.apply(Eq.any_by, index=1)

    Eq <<= Eq[-2].this.expr.apply(Algebra.Lt.of.Lt.Ge), Eq[-1].this.expr.apply(Algebra.Gt.of.Ge.Lt)

    Eq <<= Eq[-2] & Eq[1], Eq[-1] & Eq[0]

    Eq << ~(~Eq.any_ax & ~Eq.any_by)





if __name__ == '__main__':
    run()

# created on 2021-05-18
# updated on 2023-05-18
