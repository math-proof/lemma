from util import *


def extract(p_polynomial, x, y):
    assert x.shape == y.shape
    n, = p_polynomial.shape

    if p_polynomial.is_Stack:
        (b, e), (k, *_) = p_polynomial.of(Stack[Pow])
    else:
        b, (e, (k, *_)) = p_polynomial.of(Pow[Stack])

    assert not b.has(k)
    assert not b.is_given
    assert not x._has(b) and not y._has(b)
    assert e.as_poly(k).degree() == 1
    return x, y

@apply
def apply(given):
    (p, x), (S[p], y) = given.of(Equal[MatMul[2]])
    return Equal(*extract(p, x, y))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor, Bool

    p = Symbol(complex=True, zero=False)
    n, k = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), complex=True, given=True)
    Eq << apply(Equal(Stack[k:n](p ** k) @ x, Stack[k:n](p ** k) @ y))

    i = Symbol(domain=Range(1, n + 1))
    Eq << Eq[0].subs(p, i)

    Eq << Bool.All.of.Cond.apply(Eq[-1], i)

    Eq << Tensor.EqStackS.of.All_Eq.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Tensor.Stack_Dot.eq.DotSliceS)

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack_Dot.eq.DotSliceS)

    Eq << Eq[-1].T

    Eq << Eq[-1].this.find(Add[Stack]).apply(Tensor.Add_Stack.eq.Stack_Add).this.find(Pow[Stack]).apply(Tensor.Pow.eq.Stack, simplify=None)

    Eq.statement = Eq[-1].this.find(Add[Stack]).apply(Tensor.Add_Stack.eq.Stack_Add).this.find(Pow[Stack]).apply(Tensor.Pow.eq.Stack, simplify=None)

    i, k = Eq.statement.lhs.args[1].variables
    Eq << Discrete.DetStackPowAdd.eq.Prod_Factorial.vandermonde.apply(Det(Stack[i:n, k:n]((i + 1) ** k)))

    Eq << Unequal(Eq[-1].rhs, 0, plausible=True)

    Eq << Eq[-1].subs(Eq[-2].reversed)



    Eq << Tensor.EqDot.of.Ne_0.Eq.apply(Eq[-1], Eq.statement)





if __name__ == '__main__':
    run()
# created on 2020-08-21
# updated on 2023-08-27

