from util import *


@apply
def apply(le):
    (fx, *limits), M = le.of(Inf >= Expr)
    return All(fx >= M, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra

    y, m, M, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:Interval(m, M, left_open=True, right_open=True)](f(x)) >= y)

    z = Symbol(Eq[0].lhs)
    Eq << z.this.definition

    Eq <<= Algebra.All.Ge.of.Eq_Inf.apply(Eq[-1]), Eq[0].subs(Eq[-1].reversed)

    Eq <<= Algebra.All.And.of.Cond.All.apply(Eq[-2], Eq[-1], simplify=None)
    Eq <<= Eq[-1].this.expr.apply(Algebra.Ge.of.Ge.Ge)


if __name__ == '__main__':
    run()
# created on 2019-04-06
