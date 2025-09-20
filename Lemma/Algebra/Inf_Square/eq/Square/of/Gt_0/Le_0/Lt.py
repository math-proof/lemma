from util import *


@apply
def apply(lt_zero, is_nonpositive, lt, left_open=True, right_open=True, x=None):
    a = lt_zero.of(Expr > 0)
    M = is_nonpositive.of(Expr <= 0)
    m, S[M] = lt.of(Less)
    if x is None:
        x = lt.generate_var(real=True)

    self = Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2 * a)
    return Equal(self, M ** 2 * a)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a > 0, M <= 0, m < M, x=x)

    Eq << Algebra.Inf_Square.eq.Square.of.Le_0.Lt.apply(Eq[1], Eq[2])

    Eq << Algebra.Inf.eq.Mul.of.Gt_0.apply(Eq[0], Eq[-1].lhs)

    Eq << Eq[-1].subs(Eq[-2])





if __name__ == '__main__':
    run()
# created on 2021-10-02
