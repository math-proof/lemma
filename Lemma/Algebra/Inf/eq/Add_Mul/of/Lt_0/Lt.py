from util import *


@apply
def apply(is_negative, lt, fx, x=None, left_open=True, right_open=True):
    m, M = lt.of(Less)
    a = is_negative.of(Expr < 0)
    p = fx.as_poly(x)
    assert p.degree() == 1
    assert a == p.nth(1)
    b = p.nth(0)

    return Equal(Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](fx), a * M + b)


@prove
def prove(Eq):
    from Lemma import Algebra

    m, M, a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a < 0, m < M, a * x + b, x)

    Eq << Eq[-1].this.lhs.apply(Algebra.Inf.eq.Add)

    Eq << Algebra.Div.lt.Zero.of.Lt_0.apply(Eq[0])

    Eq << Algebra.Inf.eq.Mul.Sup.of.Lt_0.apply(Eq[0], Eq[-2].lhs)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Algebra.Eq.given.Eq.Div.apply(Eq[-1], a)

    Eq << Algebra.EqSup.of.Lt.apply(Eq[1], x)












if __name__ == '__main__':
    run()
# created on 2020-01-22
