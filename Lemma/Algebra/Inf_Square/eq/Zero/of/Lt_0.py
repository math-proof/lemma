from util import *


@apply
def apply(given, x):
    m = given.of(Expr < 0)
    assert not m.is_integer
    return Equal(Inf[x:m:0](x ** 2), 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    m, x = Symbol(real=True)
    Eq << apply(m < 0, x)

    Eq << Algebra.Inf_Square.even_function.apply(x ** 2, Interval.open(m, 0), x)

    Eq << -Eq[0]

    Eq << Algebra.Inf_Square.eq.Zero.of.Gt_0.apply(Eq[-1], x=x)

    Eq << Eq[-3].subs(Eq[-1]).reversed





if __name__ == '__main__':
    run()
# created on 2019-12-21
# updated on 2023-05-04
