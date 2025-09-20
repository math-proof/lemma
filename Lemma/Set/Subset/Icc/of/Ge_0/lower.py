from util import *


@apply
def apply(given, lower, left_open=False, right_open=False):
    a = given.of(Expr >= 0)
    kwargs = {'right_open' : right_open, 'left_open': left_open}
    return Subset(Interval(lower, -a, **kwargs), Interval(lower, a, **kwargs))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x >= 0, z, left_open=True)

    Eq << Set.Icc.subset.Icc_Abs.lower.apply(Eq[1].lhs)

    Eq << Algebra.EqAbs.of.Ge_0.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-07-10
