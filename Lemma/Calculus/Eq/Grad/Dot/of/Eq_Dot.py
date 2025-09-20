from util import *


@apply
def apply(eq_y, L):
    (x, WT), y = eq_y.of(Equal[MatMul])
    W = WT.T
    return Equal(Derivative[x](L(x @ W.T)), Derivative[y](L(y)) @ W)


@prove
def prove(Eq):
    from Lemma import Calculus, Tensor

    # seq_length, hidden-size, output-hidden-size
    n, d, h = Symbol(integer=True, positive=True)
    x = Symbol(shape=(n, d), real=True)
    W = Symbol(shape=(h, d), real=True)
    y = Symbol(shape=(n, h), real=True)
    L = Function(shape=(), real=True)
    Eq << apply(
        Equal(y, x @ W.T), L)

    Eq << Eq[1].this.lhs.apply(Calculus.Grad.eq.Stack)

    Eq << Eq[-1].this.rhs.find(Derivative).apply(Calculus.Grad.eq.Stack)

    Eq << Eq[-1].this.lhs.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS, simplify=None)





if __name__ == '__main__':
    run()
# created on 2024-02-13
# updated on 2024-02-15
