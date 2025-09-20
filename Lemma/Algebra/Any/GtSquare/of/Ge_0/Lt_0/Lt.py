from util import *


@apply
def apply(M_is_nonnegative, is_negative, lt, x=None):
    M = M_is_nonnegative.of(Expr >= 0)
    mM = is_negative.of(Expr < 0)
    m = mM - M

    U, m2 = lt.of(Less)
    S[m] = m2.of(Expr ** 2)

    if x is None:
        x = lt.generate_var(real=True)
    else:
        assert not x.is_integer

    return Any[x:m:M](x ** 2 > U)


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    m, M, U = Symbol(real=True, given=True)
    Eq << apply(M >= 0, m + M < 0, U < m ** 2)

    Eq << -Eq[0]

    Eq << -Eq[1].this.apply(Algebra.Lt.transport).reversed

    Eq << Algebra.Any.GtSquare.of.Le_0.Lt.Lt.apply(Eq[-2], Eq[-1], Eq[2])

    Eq << Set.Subset.Icc.of.Ge_0.lower.apply(Eq[0], m, left_open=True, right_open=True)

    Eq << Set.Any.of.Subset.Any.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2019-07-11
