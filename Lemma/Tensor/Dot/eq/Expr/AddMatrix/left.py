from util import *


@apply
def apply(x, lamda, w=None):
    n, = x.shape
    i, j = Symbol(domain=Range(n))

    if w is None:
        w = Symbol(Stack[j, i](AddMatrix(n, i, j, lamda)))
        w_quote = Symbol(Stack[j, i](AddMatrix(n, i, j, -lamda)))
    else:
        assert w[i, j] == AddMatrix(n, i, j, lamda)
        assert w_quote[i, j] == AddMatrix(n, i, j, -lamda)

    return Equal(w_quote[i, j] @ w[i, j] @ x, x)


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor
    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), real=True)
    lamda = Symbol(real=True)
    Eq << apply(x, lamda)

    i, j = Eq[0].lhs.indices

    w_quote = Eq[0].lhs.base
    w = Eq[1].lhs.base

    Eq << (w[i, j] @ x).this.subs(Eq[1])

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.expr.args[1]().expr.simplify()

    Eq << (w_quote[i, j] @ Eq[-1]).this.rhs.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.expr.simplify(wrt=j)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-11-11
