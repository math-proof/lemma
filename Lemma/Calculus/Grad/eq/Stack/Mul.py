from util import *


@apply
def apply(self, i=None):
    expr, *limits_d = self.of(Derivative)
    (x, S[1]), = limits_d
    if i is None:
        i = self.generate_var(integer=True)

    vars = set()
    for xj in expr.finditer(Indexed):
        if xj._has(x):
            x, j = xj.of(Indexed)
            vars.add(j)
    j, = vars
    expr = expr._subs(x[j], x[i])
    assert not expr._has(j)
    n, = x.shape
    return Equal(self, Stack[i:n](KroneckerDelta(i, j) * Derivative[x[i]](expr)))


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Tensor

    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    x = Symbol(real=True, shape=(n,))
    j = Symbol(integer=True)
    Eq << apply(Derivative[x](f(x[j])))

    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)

    Eq << Eq[-1].this.lhs.apply(Calculus.Grad.eq.Mul.Grad)


if __name__ == '__main__':
    run()
# created on 2023-03-19
