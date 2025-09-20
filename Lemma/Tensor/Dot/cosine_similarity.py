from util import *


@apply
def apply(x, y):
    n, = x.shape
    S[n], = y.shape
    return Equal(x @ y, y @ x)


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor
    n = Symbol(integer=True)
    x, y = Symbol(shape=(n,), real=True)
    i = Symbol(domain=Range(n))
    Eq << apply(x, y)

    Eq << Eq[0].lhs.this.apply(Tensor.Dot.eq.Sum, var=i)

    Eq << Eq[0].rhs.this.apply(Tensor.Dot.eq.Sum, var=i)

    Eq << Eq[-2].subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()
# created on 2020-08-16
