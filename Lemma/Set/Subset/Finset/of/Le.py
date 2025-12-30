from util import *


@apply
def apply(given):
    a, b = given.of(LessEqual)
    return Subset({b, a}, Interval(a, b))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    Eq << Set.Subset.given.All_In.apply(Eq[1])

    Eq << Eq[-1].this.apply(Bool.AllIn_Insert.Is.And_All)

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq <<= Set.In_Ico.given.Le.Lt.apply(Eq[-2]), Set.In_Ico.given.Le.Lt.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2023-10-22
