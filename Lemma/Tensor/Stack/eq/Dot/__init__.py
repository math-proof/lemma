from util import *


@apply
def apply(lamda):
    ((A, b), (k, *k_m)), *j_limit, (i, *i_n) = lamda.of(Stack[Sum[Mul]])

    if b._has(i):
        A, b = b, A
        assert not b._has(i)

    if not k_m:
        domain = b.domain_defined(k) & A.domain_defined(k)
        k_m = domain.of(Range)
    A = Stack(A, (k, *k_m), (i, *i_n)).simplify()

    if j_limit:
        b = Stack(b, *j_limit, (k, *k_m)).simplify()
    else:
        b = Stack(b, (k, *k_m)).simplify()

    return Equal(lamda, A @ b, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    i, j, k = Symbol(integer=True)
    n, m, d = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, m), real=True)
    # b = Symbol(real=True, shape=(m,))
    # Eq << apply(Stack[i:n](Sum[j:m](A[i, j] * b[j])))

    B = Symbol(real=True, shape=(m, d))
    Eq << apply(Stack[j:d, i:n](Sum[k:m](A[i, k] * B[k, j])))
    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()

# created on 2020-11-09

from . import swapn
