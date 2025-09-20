from util import *


@apply
def apply(le, M=None):
    (fx, *limits), M0 = le.of(Inf > Expr)
    if M is None:
        M = le.generate_var(real=True, var='M')
    return Any[M:Interval.open(M0, oo)](All(fx >= M, *limits))


@prove
def prove(Eq):
    from Lemma import Algebra

    M, M0, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:Interval(a, b, left_open=True, right_open=True)](f(x)) > M0, M)

    Eq << Algebra.Any.All.Gt.of.GtInf.apply(Eq[0])

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Ge.of.Gt.relax)


if __name__ == '__main__':
    run()
# created on 2019-01-05
