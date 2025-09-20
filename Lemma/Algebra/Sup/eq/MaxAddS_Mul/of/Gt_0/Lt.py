from util import *


@apply
def apply(is_positive, lt, fx, x=None, left_open=True, right_open=True):
    m, M = lt.of(Less)
    a = is_positive.of(Expr > 0)
    p = fx.as_poly(x)
    assert p.degree() == 1
    assert a == p.nth(1)
    b = p.nth(0)

    return Equal(Sup[x:Interval(m, M, left_open=left_open, right_open=right_open)](fx), Max(a * m + b, a * M + b))


@prove
def prove(Eq):
    from Lemma import Algebra

    m, M, x, a, b = Symbol(real=True, given=True)
    Eq << apply(a > 0, m < M, a * x + b, x)



    Eq << Algebra.LtMul.of.Gt_0.Lt.apply(Eq[0], Eq[1])

    Eq << Algebra.EqMax.of.Lt.apply(Eq[-1]) + b

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Max)
    Eq << Algebra.Sup.eq.Add_Mul.of.Gt_0.Lt.apply(Eq[0], Eq[1], a * x + b, x)
    Eq << Eq[-1].subs(Eq[-2].reversed)


if __name__ == '__main__':
    run()
# created on 2019-09-11

