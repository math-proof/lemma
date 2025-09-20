from util import *


@apply
def apply(x, lamda, w=None):
    n = x.shape[0]
    i = Symbol(domain=Range(n))

    if w is None:
        w = Symbol(Stack[i](MulMatrix(n, i, lamda)))
        w_quote = Symbol(Stack[i](MulMatrix(n, i, 1 / lamda)))
    else:
        assert w[i] == MulMatrix(n, i, lamda)
        assert w_quote[i] == MulMatrix(n, i, 1 / lamda)

    return Equal(w_quote[i] @ w[i] @ x, x)


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor
    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), real=True)
    lamda = Symbol(real=True)
    Eq << apply(x, lamda)

    i, *_ = Eq[0].lhs.indices

    w_quote = Eq[0].lhs.base
    w = Eq[1].lhs.base

    Eq << (w[i] @ x).this.subs(Eq[1])

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << (w_quote[i] @ Eq[-1]).this.rhs.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS, simplify=None)

    Eq << Eq[-1].this.find(Mul).expand()


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-11-12
