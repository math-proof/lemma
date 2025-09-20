from util import *


def sigmar2(args):
    result = []
    for i in range(1, len(args)):
        for j in range(i):
            result.append(Re(~args[i] @ args[j]) * 2)
    return Add(*result)

@apply
def apply(self):
    args = self.of(Norm[Add] ** 2)
    return Equal(self, Add(*(Norm(arg) ** 2 for arg in args), sigmar2(args)))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor

    n = Symbol(integer=True, positive=True)
    x, y, z = Symbol(complex=True, shape=(n,))
    Eq << apply(Norm(x + y + z) ** 2)

    Eq << Eq[-1].lhs.this.apply(Tensor.Square.Norm.eq.Dot.Conj)

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Add, deep=True)

    Eq << Eq[-1].this.rhs.args[0].apply(Tensor.Dot.eq.Square.Norm)

    Eq << Eq[-1].this.rhs.args[:4:2].apply(Algebra.Add.eq.Mul.Re)

    Eq << Eq[-1].this.rhs.args[1].apply(Tensor.Dot.eq.Square.Norm)

    Eq << Eq[-1].this.rhs.args[:4:2].apply(Algebra.Add.eq.Mul.Re)

    Eq << Eq[-1].this.rhs.args[:2].apply(Algebra.Add.eq.Mul.Re)

    Eq << Eq[-1].this.rhs.args[0].apply(Tensor.Dot.eq.Square.Norm)

    Eq << Eq[-1].this.find(MatMul).T

    Eq << Eq[-1].this.find(Mul[2]).find(MatMul).T

    Eq << Eq[-1].this.find(MatMul).T


if __name__ == '__main__':
    run()
# created on 2023-06-24
