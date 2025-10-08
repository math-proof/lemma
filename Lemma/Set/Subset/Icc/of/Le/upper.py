from util import *


@apply
def apply(given, upper, left_open=False, right_open=False):
    a, b = given.of(LessEqual)
    kwargs = {'right_open' : right_open, 'left_open': left_open}
    return Subset(Interval(b, upper, **kwargs), Interval(a, upper, **kwargs))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x <= y, z, left_open=True)

    Eq << Set.Subset.given.All_In.apply(Eq[1])

    Eq << Eq[-1].this.expr.apply(Set.In_Ico.given.Ge.Lt)

    Eq << Bool.All_And.given.All.All.apply(Eq[-1])

    Eq <<= Bool.All.given.All_Or_Not.apply(Eq[-2]), Bool.All.given.All_Or_Not.apply(Eq[-1])

    Eq <<= Eq[-2].this.find(NotElement).apply(Set.NotIn_Icc.given.OrLtS), Eq[-1].this.find(NotElement).apply(Set.NotIn_Icc.given.OrLtS)

    Eq << Algebra.Or.given.Or.apply(Eq[-1], slice(0, 3, 2))

    Eq << Set.Or.given.NotIn.Icc.apply(Eq[-1])

    Eq << Set.Eq_Empty.Icc.of.Le.apply(Eq[0], left_open=True)

    Eq << Eq[-2].subs(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2019-09-06
# updated on 2023-05-14
