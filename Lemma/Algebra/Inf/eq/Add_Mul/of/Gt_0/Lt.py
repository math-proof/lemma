from util import *


@apply
def apply(is_positive, lt, fx, x=None, left_open=True, right_open=True):
    m, M = lt.of(Less)
    p = fx.as_poly(x)
    assert p.degree() == 1
    a = is_positive.of(Expr > 0)
    assert a == p.nth(1)
    b = p.nth(0)

    return Equal(Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](fx), a * m + b)


@prove
def prove(Eq):
    from Lemma import Algebra

    m, M, a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a > 0, m < M, a * x + b, x)

    Eq << Eq[-1].this.lhs.apply(Algebra.Inf.eq.Add)

    Eq << Algebra.Div.gt.Zero.of.Gt_0.apply(Eq[0])

    Eq << Algebra.Inf.eq.Mul.of.Gt_0.apply(Eq[-1], Eq[-2].lhs) * a

    Eq << Eq[-3].subs(Eq[-1].reversed)

    Eq << Algebra.Eq.given.Eq.Div.apply(Eq[-1], a)

    Eq << Algebra.EqInf.of.Lt.apply(Eq[1], x)










if __name__ == '__main__':
    run()
# created on 2019-08-27

