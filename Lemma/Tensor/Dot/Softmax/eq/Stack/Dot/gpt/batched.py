from util import *


@apply
def apply(self, i):
    (((Q, KT), d_sqrt), ((_n,), (S[0],))), V = self.of(Softmax[Expr @ Expr / Expr + (BandPart[Ones] - 1) * Infinity] @ Expr)
    n = V.shape[-2]
    assert _n >= n - 1
    K = KT.T
    return Equal(self, Transpose[0, 1](Stack[i:n](Softmax((Q[:, i] @ K[:, :i + 1].T) / d_sqrt) @ V[:, :i + 1])))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    m, n, d_z = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Q, K, V = Symbol(shape=(m, n, d_z), real=True)
    Eq << apply(softmax(Q @ K.T / sqrt(d_z) + (BandPart[n, 0](Ones(n, n)) - 1) * oo) @ V, i)

    k = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], k)

    Eq << Eq[-1].this.lhs.apply(Tensor.DotSoftmax.eq.Stack_Dot.gpt, i)
    # https://s3-us-west-2.amazonaws.com/openai-assets/research-covers/language-unsupervised/language_understanding_paper.pdf



if __name__ == '__main__':
    run()
# created on 2024-02-29
