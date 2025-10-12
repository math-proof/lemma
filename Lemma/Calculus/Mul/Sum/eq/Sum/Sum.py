from util import *


@apply
def apply(A, B, n=None, k=None, x=None):

    if x is None:
        x = Symbol(real=True)

    if n is None:
        n = Symbol(integer=True)
    if k is None:
        k = Symbol(integer=True)

    return Equal(Sum[n:oo](A[n] * x ** n) * Sum[n:oo](B[n] * x ** n), Sum[n:oo](Sum[k:n + 1](A[n - k] * B[k]) * x ** n))


@prove
def prove(Eq):
    from Lemma import Algebra, Finset

    A, B = Symbol(shape=(oo,), real=True)
    Eq << apply(A, B)

    Eq << Eq[0].lhs.this.apply(Finset.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-1].this.rhs.expr.apply(Finset.Mul_Sum.eq.Sum_Mul)

    i, n = Eq[-1].rhs.variables
    k = Eq[0].rhs.expr.args[1].variable
    Eq << Eq[-1].this.rhs.limits_subs(i, k)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.swap)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.subst.offset, -k)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.swap.intlimit)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.separate)


if __name__ == '__main__':
    run()
    # created on 2020-06-28
