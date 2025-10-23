from util import *


@apply
def apply(self):
    y, x, i, n = dissect_distance(self)
    return Equal(self, abs(Sum[i:n](y - x[i])) / n)


def dissect_distance(variance):
    ym, ((xi, (i, *ab)), n) = variance.of(Abs[Expr - Sum / Expr])
    x = Stack[i](xi).simplify()
    if ab:
        S[0], S[n] = ab

    return ym, x, i, n


@prove
def prove(Eq):
    from Lemma import Algebra, Finset

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    y = Symbol(real=True)
    i = Symbol(integer=True)
    Eq << apply(abs(y - Sum[i](x[i]) / n))

    Eq << Eq[0].this.rhs.find(Sum).simplify()

    x_ = Symbol("x", Stack[i](y - x[i]))
    Eq << x_[i].this.definition

    Eq << Eq[-1] - y

    Eq << -Eq[-1]

    Eq << Eq[0].lhs.this.subs(Eq[-1].reversed)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.rhs.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].subs(x_[i].this.definition)


if __name__ == '__main__':
    run()
# created on 2018-08-02
