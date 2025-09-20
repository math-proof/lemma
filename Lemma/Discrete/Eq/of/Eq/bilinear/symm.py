from util import *


@apply
def apply(given, x, y):
    W, S[W.T] = given.of(Equal)

    return Equal(x @ W @ y, y @ W @ x)


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    n = Symbol(integer=True)
    x, y = Symbol(shape=(n,), real=True)
    W = Symbol(shape=(n, n), real=True)
    Eq << apply(Equal(W, W.T), x, y)

    Eq << Tensor.Dot.bilinear.Transpose.apply(Eq[1].lhs)

    Eq << Eq[-1].this.rhs.subs(Eq[0])





if __name__ == '__main__':
    run()
# created on 2021-01-04
# updated on 2023-05-21
