from util import *


@apply
def apply(lt_zero, ge_zero, lt, x=None):
    a = lt_zero.of(Expr > 0)
    m = ge_zero.of(Expr >= 0)
    S[m], M = lt.of(Less)
    if x is None:
        x = lt.generate_var(real=True)

    return Equal(Min(m ** 2 * a, M ** 2 * a), m ** 2 * a)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a > 0, m >= 0, m < M, x=x)

    Eq << Algebra.EqMin.of.Ge_0.Lt.apply(Eq[1], Eq[2])

    Eq << Algebra.Min.eq.Mul.of.Gt_0.apply(Eq[0], Eq[-1].lhs)

    Eq << Eq[-1].subs(Eq[-2])





if __name__ == '__main__':
    run()
# created on 2021-10-02
