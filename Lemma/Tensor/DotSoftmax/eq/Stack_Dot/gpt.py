from util import *


@apply
def apply(self, i):
    (((Q, KT), d_sqrt), ((_n,), (S[0],))), V = self.of(Softmax[Expr @ Expr / Expr + (BandPart[Ones] - 1) * Infinity] @ Expr)
    n = V.shape[0]
    assert _n >= n - 1
    K = KT.T
    return Equal(self, Stack[i:n](Softmax((Q[i] @ K[:i + 1].T) / d_sqrt) @ V[:i + 1]))


@prove
def prove(Eq):
    from Lemma import Tensor

    n, d_z = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Q, K, V = Symbol(shape=(n, d_z), real=True)
    Eq << apply(softmax(Q @ K.T / sqrt(d_z) + (BandPart[n, 0](Ones(n, n)) - 1) * oo) @ V, i)

    β = Symbol(Stack[i:n](relu(i - n)))
    ζ = Symbol(Stack[i:n](Min(i + 1, n)))
    Eq << β.this.definition

    Eq << ζ.this.definition

    Eq << Tensor.Eq.Dot.Softmax.of.Eq_Relu.Eq_Min.band_part_mask.bert.apply(*Eq[-2:], Q, K, V)

    Eq << Eq[1].this.rhs().expr.defun()

    Eq << Eq[2].this.rhs().expr.simplify()

    Eq << Eq[-3].subs(*Eq[-2:])

    # https://s3-us-west-2.amazonaws.com/openai-assets/research-covers/language-unsupervised/language_understanding_paper.pdf


if __name__ == '__main__':
    run()
# created on 2023-06-18
# updated on 2023-08-28
