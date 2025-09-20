from util import *


@apply
def apply(given, m, i=None):
    (x, w), y = given.of(Equal[MatMul])
    n, = x.shape
    _i, _j = w.of(SwapMatrix)
    assert 0 <= _i < n
    assert 0 <= _j < n
    if i is None:
        i = given.generate_var(integer=True, var='i')

    return Equal(Sum[i:n](x[i] ** m), Sum[i:n](y[i] ** m))


@prove(proved=False)
def prove(Eq):
    from Lemma import Discrete, Tensor

    m = Symbol(integer=True, positive=True, given=False)
    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True, given=True)
    i, j = Symbol(domain=Range(n))
    Eq << apply(Equal(x @ SwapMatrix(n, i, j), y), m)

    Eq.initial = Eq[1].subs(m, 1)

    _i = Eq[1].lhs.variable
    Eq << Tensor.EqSum.of.Eq_Dot.apply(Eq[0], _i)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.simplify()

    Eq.induct = Eq[1].subs(m, m + 1)



if __name__ == '__main__':
    run()
# created on 2020-10-31
