from util import *


@apply
def apply(self):
    (x, W), (β, (S[x], B, A)) = self.of(Expr @ Expr + Expr * (Expr @ Expr @ Expr))
    return Equal(self, x @ Transpose(W.T + β * A.T @ B.T, evaluate=False))

@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor

    # n denotes sequence length (seq_length)
    # d denotes embedding size
    n, d, d_row, a = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n, d))
    W = Symbol(real=True, shape=(d_row, d))
    B = Symbol(real=True, shape=(d, a))
    A = Symbol(real=True, shape=(a, d_row))
    β = Symbol(real=True)
    Eq << apply(x @ W.T + (x @ B @ A) * β)

    W_quote = Symbol(W + β * A.T @ B.T)
    Eq << W_quote.this.definition

    Eq <<= Eq[-1].reversed, Algebra.EqTranspose.of.Eq.apply(Eq[-1])

    Eq << Eq[0].subs(*Eq[-2:])

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Add)

    # https://arxiv.org/abs/2106.09685


if __name__ == '__main__':
    run()
# created on 2023-12-02
