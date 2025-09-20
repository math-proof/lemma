from util import *


@apply
def apply(given):
    (x, p_polynomial), (y, S[p_polynomial]) = given.of(Equal[MatMul[2]])
    from Lemma.Tensor.Eq.of.EqDotSStack_Pow.independence.vector import extract
    return Equal(*extract(p_polynomial, x, y))


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    p = Symbol(complex=True, zero=False)
    n, k = Symbol(domain=Range(1, oo))
    x, y = Symbol(shape=(n,), given=True, complex=True)
    Eq << apply(Equal(x @ Stack[k:n](p ** k), y @ Stack[k:n](p ** k)))

    Eq << Tensor.Dot.cosine_similarity.apply(*Eq[0].lhs.args)

    Eq << Tensor.Dot.cosine_similarity.apply(*Eq[0].rhs.args)

    Eq << Eq[0].subs(Eq[-1], Eq[-2])

    Eq << Tensor.Eq.of.EqDotSStack_Pow.independence.vector.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2020-08-22
# updated on 2023-04-08
