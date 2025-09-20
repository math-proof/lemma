from util import *


@apply
def apply(self):
    mul, *limits = self.of(Sum)
    from Lemma.Algebra.Mul_Add.eq.AddMulS import convert
    add = convert(mul)

    from Lemma.Algebra.Sum_Add.eq.AddSumS import associate
    rhs = associate(Sum, Sum(add, *limits))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    f, h, g = Function(real=True)
    Eq << apply(Sum[i:n]((f(i) + h(i)) * g(i)))

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Mul_Add.eq.AddMulS)
    Eq << Eq[-1].this.lhs.apply(Algebra.Sum_Add.eq.AddSumS)


if __name__ == '__main__':
    run()

# created on 2020-03-27

