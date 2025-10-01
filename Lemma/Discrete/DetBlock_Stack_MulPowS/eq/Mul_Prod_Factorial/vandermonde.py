from util import *


@apply
def apply(self):
    (((j, i), (x1, S[j])), (S[j], S[0], m), (S[i], S[0], d)), (((S[j], S[i]), ((x2, S[j]))), (S[j], S[0], S[m]), (S[i], S[0], S[m - d])) = self.of(Det[BlockMatrix[Stack[Pow * Pow], Stack[Pow * Pow]]])
    assert m > d + 1
    return Equal(self, x2 ** Binomial(m - d, 2) * x1 ** Binomial(d, 2) * (x2 - x1) ** (d * (m - d)) * Product[i:d](factorial(i)) * Product[i:m - d](factorial(i)))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Logic, Tensor

    d = Symbol(integer=True, positive=True)
    m = Symbol(domain=Range(d + 2, oo))
    i, j = Symbol(integer=True)
    x1, x2 = Symbol(complex=True)
    Eq << apply(Det(BlockMatrix([Stack[j:m, i:d](j ** i * x1 ** j), Stack[j:m, i:m - d](j ** i * x2 ** j)])))

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[0], cond=Equal(x2, 0))

    Eq << Eq[-1].this.lhs.apply(Discrete.Eq.Det.Block.eq.Mul.Prod.of.Ne_0.vandermonde.mn, x1, m, d)

    Eq << Logic.Imp.given.ImpEq.apply(Eq[-2])

    Eq << Eq[-1].this.find(Stack[2]).apply(Tensor.Stack.eq.Transpose.Block, 1)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.Transpose.Block, 1)

    Eq << Eq[-1].this.find(BlockMatrix).args[1].find((~Stack) * Stack)().expr.simplify()

    Eq << Eq[-1].this.find(Det).apply(Discrete.Det.Block.eq.Zero)





if __name__ == '__main__':
    run()
# created on 2022-07-11
# updated on 2023-03-18

