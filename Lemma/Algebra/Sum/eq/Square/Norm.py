from util import *


@apply
def apply(self):
    xi, (i, S[0], n) = self.of(Sum[Expr ** 2])
    x = Stack[i:n](xi).simplify()
    return Equal(self, Norm(x) ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    i = Symbol(integer=True)
    Eq << apply(Sum[i:n](x[i] * x[i]))

    Eq << Eq[0].this.find(Norm).apply(Algebra.Norm.eq.Sqrt)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.domain_defined)


if __name__ == '__main__':
    run()
# created on 2023-06-29
