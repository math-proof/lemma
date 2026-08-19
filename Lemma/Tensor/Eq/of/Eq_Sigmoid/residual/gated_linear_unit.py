from util import *


@apply
def apply(eq):
    (x, (hx, fx)), gx = eq.of(Equal[Symbol + Mul[sigmoid]])
    assert x.is_symbol
    assert gx._has(x) and fx._has(x) and hx._has(x)
    n, = x.shape
    return Equal(
        Derivative[x](gx),
        Identity(*x.shape) +  Derivative[x](fx) * (sigmoid(fx) * (1 - sigmoid(fx)) * Ones(n, n)).T * hx + sigmoid(fx) * Derivative[x](hx))


@prove
def prove(Eq):
    from Lemma import Real

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    f, g, h = Function(real=True, shape=(n,))
    Eq << apply(Equal(g(x), x + h(x) * sigmoid(f(x))))

    Eq << Real.EqGrad.of.Eq.apply(Eq[0], (x,))

    Eq << Eq[-1].this.rhs.apply(Real.Grad.eq.Add)

    Eq << Eq[-1].this.find(Derivative[sigmoid]).apply(Real.Grad.Sigmoid.eq.Mul.Sigmoid.vector)







if __name__ == '__main__':
    run()
# created on 2021-12-22
# updated on 2023-03-18
