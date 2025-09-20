from util import *


@apply
def apply(is_nonpositive, lt, left_open=True, right_open=True, x=None):
    M = is_nonpositive.of(Expr <= 0)
    m, S[M] = lt.of(Less)
    if x is None:
        x = lt.generate_var(real=True)

    self = Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, M ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(M <= 0, m < M, x=x)

    Eq << Algebra.Inf_Square.even_function.apply(x ** 2, Interval.open(m, M), x)

    Eq <<= -Eq[0], -Eq[1].reversed

    Eq << Algebra.Inf_Square.eq.Square.of.Ge_0.Lt.apply(Eq[-2], Eq[-1])

    Eq << Eq[-4].subs(Eq[-1]).reversed




if __name__ == '__main__':
    run()
# created on 2019-12-08
# updated on 2023-05-06
