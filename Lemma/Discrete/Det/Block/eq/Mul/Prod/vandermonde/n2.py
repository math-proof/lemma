from util import *


@apply
def apply(self):
    ((x1, j), j_limit), ((S[j], (S[x1], S[j])), S[j_limit]), (((S[j], i), (x2, S[j])), S[j_limit], (S[i], S[0], n)) = self.of(Det[BlockMatrix[Stack[Pow], Stack[Symbol * Pow], Stack[Pow * Pow]]])

    S[j], S[0], S[n + 2:n >= 1] = j_limit

    return Equal(self, x1 * x2 ** Binomial(n, 2) * (x2 - x1) ** (2 * n) * Product[i:n](factorial(i)))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Logic, Tensor

    n = Symbol(domain=Range(2, oo))
    x1, x2 = Symbol(complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(Det([Stack[j:n + 2](x1 ** j), Stack[j:n + 2](j * x1 ** j), Stack[j:n + 2, i:n](j ** i * x2 ** j)]))

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[0], cond=Equal(x2, 0))

    Eq << Eq[-1].this.lhs.apply(Discrete.Eq.Det.Block.eq.Mul.Prod.of.Ne_0.vandermonde.n2, n, x1)

    Eq << Logic.Imp.given.Imp.subst.apply(Eq[-2])

    Eq << Eq[-1].this.find(Stack[2]).apply(Tensor.Stack.eq.Block.shift)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.Block.shift)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.Transpose.Block, 1)

    Eq << Eq[-1].this.find((~Stack) * Stack)().expr.simplify()

    Eq << Eq[-1].this.find(Det).apply(Discrete.Det.Block.eq.Zero)





if __name__ == '__main__':
    run()
# created on 2021-11-22
# updated on 2023-03-18
