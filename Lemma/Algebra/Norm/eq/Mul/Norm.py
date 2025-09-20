from util import *


@apply
def apply(self):
    args = self.of(Norm[Mul])
    vector, coeffs = std.array_split(args, lambda arg: arg.shape)
    return Equal(self, abs(Mul(*coeffs)) * Norm(Mul(*vector)))


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    a = Symbol(complex=True)
    Eq << apply(Norm(x * a))

    Eq << Eq[0].this.lhs.apply(Algebra.Norm.eq.Sqrt)

    Eq << Eq[-1].this.find(Norm).apply(Algebra.Norm.eq.Sqrt)

    Eq << Eq[-1].this.find(Abs ** 2).apply(Algebra.Square.Abs.eq.Mul.Conj)

    Eq << Eq[-1].this.find(Expr * Conjugate).args[:2].apply(Algebra.Mul.Conj.eq.Square.Abs)

    Eq << Eq[-1].this.find(Expr * Conjugate).apply(Algebra.Mul.Conj.eq.Square.Abs)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.domain_defined)


if __name__ == '__main__':
    run()
# created on 2023-06-24
