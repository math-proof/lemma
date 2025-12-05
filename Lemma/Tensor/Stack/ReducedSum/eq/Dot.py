from util import *


@apply
def apply(lamda):
    (A, b), (i, *i_ab) = lamda.of(Stack[ReducedSum[Mul]])

    if b._has(i):
        A, b = b, A
    assert not b._has(i)
    A = Stack(A, (i, *i_ab)).simplify()

    rhs = A @ b
    return Equal(lamda, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor, Vector

    i, j = Symbol(integer=True)
    n, m = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, m), real=True)
    b = Symbol(real=True, shape=(m,))
    Eq << apply(Stack[i:n](ReducedSum(A[i] * b)))

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.lhs.apply(Vector.Sum.eq.Sum_Get)
    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()
# created on 2020-11-10
