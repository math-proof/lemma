from util import *


def sigmar2(args):
    result = []
    for i in range(1, len(args)):
        for j in range(i):
            result.append(Re(~args[i] * args[j]) * 2)
    return Add(*result)
@apply
def apply(self):
    args = self.of(Abs[Add] ** 2)
    return Equal(self, Add(*(abs(arg) ** 2 for arg in args), sigmar2(args)))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(complex=True)
    Eq << apply(abs(x + y + z) ** 2)

    Eq << Eq[-1].lhs.this.apply(Algebra.Square.Abs.eq.Mul.Conj)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS, deep=True)

    Eq << Eq[-1].this.rhs.args[0].apply(Algebra.Mul.Conj.eq.Square.Abs)

    Eq << Eq[-1].this.rhs.args[:4:2].apply(Algebra.Add.eq.Mul.Re)

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Mul.Conj.eq.Square.Abs)

    Eq << Eq[-1].this.rhs.args[:4:2].apply(Algebra.Add.eq.Mul.Re)

    Eq << Eq[-1].this.rhs.args[:2].apply(Algebra.Add.eq.Mul.Re)

    Eq << Eq[-1].this.rhs.args[0].apply(Algebra.Mul.Conj.eq.Square.Abs)




if __name__ == '__main__':
    run()
# created on 2023-06-24
