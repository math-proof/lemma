from util import *


def is_infinite_series(fx):
    f, (n, a, b) = fx.of(Sum)
    assert n.is_integer
    assert b.is_infinite
    if not a.is_zero:
        f = f._subs(n, n + a)
    return f


@apply
def apply(given, x):

    lhs, rhs = given.of(Equal)
    an = is_infinite_series(lhs)
    bn = is_infinite_series(rhs)
    n = lhs.variable
    an /= x ** n
    bn /= x ** n
    return Equal(an, bn)


@prove(proved=False)
def prove(Eq):
    from Lemma import Algebra, Calculus

    A, B = Symbol(shape=(oo,), real=True)
    x = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(Equal(Sum[n:oo](A[n] * x ** n), Sum[n:oo](B[n] * x ** n)), x=x)

    Eq << Eq[0].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq[3].subs(x, 0)

    Eq << Eq[-1].this.lhs().expr.simplify()

    Eq.initial = Eq[-1].this.rhs().expr.simplify()

    m = Symbol(integer=True, given=False, nonnegative=True)
    Eq.hypothesis = Eq[1].subs(n, m)

    Eq.induct = Eq.hypothesis.subs(m, m + 1)

    k = Symbol(domain=Range(m + 1))
    Eq.hypothesis_k = Eq.hypothesis.subs(m, k)

    Eq << Eq.hypothesis_k * x ** k

    Eq << Algebra.EqSumS.of.Eq.apply(Eq[-1], (k,))

    _k = Symbol('k', integer=True)
    Eq << Eq[-1].this.lhs.limits_subs(k, _k)

    Eq << Eq[-1].this.rhs.limits_subs(k, _k)

    Eq << Eq[3].this.lhs.limits_subs(n, _k)

    Eq << Eq[3].this.rhs.limits_subs(n, _k)

    Eq << Eq[3] - Eq[-1]

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Sum.limits.SDiff)

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Sum.limits.SDiff)

    r = Symbol(real=True, positive=True)
    Eq << Eq[-1].subs(x, r)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.subst.offset, m + 1)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.subst.offset, m + 1)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum_Mul.eq.Mul_Sum)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum_Mul.eq.Mul_Sum)

    Eq << Calculus.EqLimit.of.Eq.apply(Eq[-1], (r, 0))

    Eq << Eq[-1].this.lhs.apply(Calculus.Limit.eq.Sum)

    Eq << Eq[-1].this.rhs.apply(Calculus.Limit.eq.Sum)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.AddSumS, cond={0})

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.AddSumS, cond={0})

    Eq << Eq[-1].this.lhs.args[1]().expr.doit()

    Eq << Eq[-1].this.rhs.args[1]().expr.doit()

    Eq << Imply(Eq.hypothesis_k, Eq.induct, plausible=True)

    Eq << Logic.Cond.of.Cond.Imp.induct.second.apply(Eq.initial, Eq[-1], n=m + 1, k=k, hypothesis=True)

    Eq << Eq.hypothesis.subs(m, n)

    Eq << Logic.All.of.All_OrNot.apply(Eq[-1], 1)




if __name__ == '__main__':
    run()

# created on 2020-05-18
# updated on 2023-04-16
