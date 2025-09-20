from util import *


@apply
def apply(is_negative, lt, fx, x=None, left_open=True, right_open=True):
    m, M = lt.of(Less)
    a = is_negative.of(Expr < 0)
    p = fx.as_poly(x)
    assert p.degree() == 1
    assert a == p.nth(1)
    b = p.nth(0)

    return Equal(Sup[x:Interval(m, M, left_open=left_open, right_open=right_open)](fx), a * m + b)


@prove
def prove(Eq):
    from Lemma import Algebra

    m, M, x, a, b = Symbol(real=True, given=True)
    Eq << apply(a < 0, m < M, a * x + b, x)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sup.eq.Add)

    Eq << Algebra.Sup.eq.Mul.Inf.of.Lt_0.apply(Eq[0], Eq[-1].lhs)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Algebra.Eq.given.Eq.Div.apply(Eq[-1], a)
    Eq << Algebra.EqInf.of.Lt.apply(Eq[1], x)


if __name__ == '__main__':
    run()
# created on 2019-12-23

