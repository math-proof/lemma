from util import *


@apply
def apply(self):
    ((r, j), j_limit), ((S[j], i), S[j_limit], (S[i], S[0], n)) = self.of(Det[BlockMatrix[Stack[Pow], Stack[Pow]]])

    S[j], S[0], S[n + 1:n > 0] = j_limit

    return Equal(self, (1 - r) ** n * Product[i:n](factorial(i)))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor

    r = Symbol(real=True)
    n = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    Eq << apply(Det(BlockMatrix([Stack[j:n + 1](r ** j), Stack[j:n + 1, i:n](j ** i)])))

    j, i = Eq[0].lhs.arg.args[1].variables
    E = Stack[j:n + 1, i:n + 1]((-1) ** (j - i) * binomial(j, i))
    Eq << (Eq[0].lhs.arg @ E).this.apply(Tensor.Dot.eq.Block)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].find(Stack[Sum, Tuple[2]]).this().expr.simplify()

    Eq << Eq[-1].this.rhs.expr.apply(Discrete.Sum.Binom.eq.Mul.Stirling, simplify=None)

    Eq << Eq[3].subs(Eq[-1])

    Eq << Eq[-1].find(Stack[Sum, Tuple]).this().expr.simplify()

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Sum).apply(Discrete.Sum.Binom.eq.Pow.Newton)

    Eq << ShiftMatrix(n + 1, 0, n) @ Eq[-1]

    Eq << Discrete.EqDet.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Discrete.Det.eq.Mul)

    Eq << Eq[-1].this.find(Add ** Symbol).apply(Algebra.Pow.eq.Mul.Neg)


if __name__ == '__main__':
    run()
# created on 2021-10-04
# updated on 2022-07-11

from . import n3
