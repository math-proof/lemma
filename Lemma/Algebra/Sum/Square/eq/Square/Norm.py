from util import *


@apply
def apply(self):
    xi, (i, *ab) = self.of(Sum[Abs ** 2])
    x = Stack(xi, (i, *ab)).simplify()
    return Equal(self, Norm(x) ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    Eq << apply(Sum[i:n](abs(x[i]) ** 2))

    Eq << Eq[0].this.find(Norm).apply(Algebra.Norm.eq.Sqrt)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.domain_defined)


if __name__ == '__main__':
    run()
# created on 2023-06-24
