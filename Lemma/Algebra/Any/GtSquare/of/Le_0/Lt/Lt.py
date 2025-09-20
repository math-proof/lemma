from util import *


@apply
def apply(M_is_nonpositive, lt_mM, lt, x=None):
    M = M_is_nonpositive.of(Expr <= 0)
    m, S[M] = lt_mM.of(Less)

    U, M2 = lt.of(Less)
    S[m] = M2.of(Expr ** 2)
    if x is None:
        x = lt.generate_var(real=True)
    return Any[x:Interval(m, M, left_open=True, right_open=True)](x ** 2 > U)


@prove
def prove(Eq):
    from Lemma import Algebra

    m, M, U = Symbol(real=True, given=True)
    Eq << apply(M <= 0, m < M, U < m ** 2)

    Eq << -Eq[0]

    Eq << -Eq[1].reversed

    Eq << Algebra.Any.GtSquare.of.Ge_0.Lt.Lt.apply(Eq[-2], Eq[-1], Eq[2])

    x = Eq[-1].variable
    Eq << Algebra.Any.of.Any.limits.subst.Neg.real.apply(Eq[-1], x, -x)


if __name__ == '__main__':
    run()
# created on 2019-07-07
