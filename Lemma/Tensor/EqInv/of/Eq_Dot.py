from util import *


@apply
def apply(given, left=None):
    [*args], rhs = given.of(Equal[MatMul])
    rhs_is_invertible = rhs.is_invertible
    if left:
        X = args.pop(0)
        rhs = X.inverse() @ rhs
    else:
        X = args.pop()
        rhs = rhs @ X.inverse()
    assert rhs_is_invertible or X.is_invertible

    return Equal(MatMul(*args), rhs)


@prove
def prove(Eq):
    from Lemma import Discrete

    n = Symbol(integer=True, positive=True)
    A, B = Symbol(real=True, shape=(n, n))
    C = Symbol(real=True, shape=(n, n), singular=False)
    Eq << apply(Equal(A @ B, C))

    Eq << Discrete.EqInv.of.Eq.apply(Eq[0])

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], B)

    Eq << Discrete.EqInv.of.Eq.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2023-04-30
# updated on 2023-07-04
