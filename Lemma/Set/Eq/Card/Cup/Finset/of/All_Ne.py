from util import *


@apply
def apply(all_historic):
    (xi, xj), (j, S[0], i), (S[i], S[0], n) = all_historic.of(All[Unequal])
    if xi._has(j):
        xi, xj = xj, xi

    assert xi._subs(i, j) == xj
    setc = Cup[i:n]({xi})
    return Equal(Card(setc), n, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a = Symbol(integer=True, etype=dtype.integer)
    x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
    Eq << apply(All[j:i, i:n](Unequal(x[i], x[j])))

    @Function(real=True)
    def f(x):
        return S.One

    Eq << Algebra.EqSum.of.All_Ne.double_limits.apply(Eq[0], Sum[a:Eq[1].lhs.arg](f(a)))

    Eq << Eq[-1].this.lhs.expr.defun()
    Eq << Eq[-1].this.rhs.expr.defun()


if __name__ == '__main__':
    run()
# created on 2021-01-14
