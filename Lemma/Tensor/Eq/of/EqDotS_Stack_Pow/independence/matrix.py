from util import *


@apply
def apply(given):
    (*x, p_polynomial), (*y, S[p_polynomial]) = given.of(Equal[MatMul[2]])
    x = MatMul(*x)
    y = MatMul(*y)

    from Lemma.Tensor.Eq.of.EqDotSStack_Pow.independence.vector import extract
    x, y = extract(p_polynomial, x, y)

    if given.is_Exists:
        return Any(Equal(x, y), (x,), (y,))
    else:
        return Equal(x, y)


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor

    p = Symbol(complex=True, zero=False)
    m, n, k = Symbol(domain=Range(1, oo))
    x, y = Symbol(shape=(m, n))
    Eq << apply(Equal(x @ Stack[k:n](p ** k), y @ Stack[k:n](p ** k)))

    i = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[1], i)

    Eq << Eq[0][i]

    Eq << Tensor.Eq.of.EqDotS_Stack_Pow.independence.vector.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2020-08-22
# updated on 2023-04-08
