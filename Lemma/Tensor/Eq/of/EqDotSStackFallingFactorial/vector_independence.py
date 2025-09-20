from util import *


def extract(p_polynomial, x, y):
    assert x.shape == y.shape
    n, = p_polynomial.shape
    (b, e), (k, *_) = p_polynomial.of(Stack[FallingFactorial])

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
    from Lemma import Algebra, Discrete, Tensor, Logic

    p = Symbol(complex=True)
    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    x, y = Symbol(shape=(n,), complex=True, given=True)
    Eq << apply(Equal(Stack[k:n](FallingFactorial(p, k)) @ x, Stack[k:n](FallingFactorial(p, k)) @ y))

    i = Symbol(domain=Range(n))
    Eq << Eq[0].subs(p, i)

    Eq << Logic.All.of.Cond.apply(Eq[-1], i)

    Eq << Tensor.EqStackS.of.All_Eq.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Tensor.Stack.Dot.eq.Dot)

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack.Dot.eq.Dot)

    Eq.statement = Eq[-1].T

    Eq << Det(Eq.statement.find(Stack)).this.doit()

    Eq << Unequal(Eq[-1].rhs, 0, plausible=True)

    Eq << Eq[-1].subs(Eq[-2].reversed)

    Eq << Tensor.EqDot.of.Ne_0.Eq.apply(Eq[-1], Eq.statement)





if __name__ == '__main__':
    run()
# created on 2023-08-26
# updated on 2023-08-27
