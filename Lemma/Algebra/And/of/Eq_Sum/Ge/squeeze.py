from util import *


@apply
def apply(eq, ge):
    (xi, (i, S[0], n)), a = eq.of(Equal[Sum])
    xn, S[a] = ge.of(GreaterEqual)

    assert n > 0
    assert xn == xi._subs(i, n - 1)

    return Equal(xn, a), All[i:n - 1](Equal(xi, 0))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(real=True, negative=False, shape=(oo,), given=True)
    n = Symbol(integer=True, negative=False, given=True)
    i, j = Symbol(integer=True)
    a = Symbol(real=True, negative=False)
    Eq << apply(Equal(Sum[i:n + 1](x[i]), a), x[n] >= a)

    Eq.eq = Eq[0].this.lhs.apply(Algebra.Sum.eq.AddSumS, cond={n})

    Eq << GreaterEqual(Eq.eq.find(Sum), 0, plausible=True)

    Eq << Algebra.LeSub.of.Eq.Ge.apply(Eq.eq, Eq[-1])

    Eq << Algebra.Eq.of.Ge.Le.apply(Eq[1], Eq[-1])

    Eq << Eq.eq.subs(Eq[2]).this.apply(Algebra.EqAddS.Is.Eq)

    Eq << Eq[-1].this.lhs.limits_subs(i, j)

    Eq << ~Eq[3]

    Eq << Eq[-1].this.expr.apply(Algebra.Gt_0.of.Ne_0)

    Eq << Eq[-3].this.lhs.apply(Algebra.Sum.eq.AddSumS, cond={i})

    Eq << Logic.Any_And.of.Any.All.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this().expr.find(Piecewise, Element).simplify()

    Eq << Eq[-1].this.expr.apply(Algebra.LtSub.of.Eq.Gt)


if __name__ == '__main__':
    run()
# created on 2019-04-28
