from util import *


@apply
def apply(ne, eta=None):
    fx, (x, S[1]) = ne.of(Unequal[Derivative, Zeros])
    assert fx.is_Function
    S[x] = fx.arg
    if eta is None:
        eta = ne.generate_var(real=True, var='eta')

    return Subs[eta:0](Derivative[eta](fx._subs(x, x - eta * Derivative(fx, x)))) < 0


@prove(proved=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x = Symbol(r"\vec x", real=True, shape=(n,))
    f = Function(real=True, shape=())
    eta = Symbol(real=True)
    Eq << apply(Unequal(Derivative(f(x), x), Zeros(*x.shape)), eta)

    


if __name__ == '__main__':
    run()
# created on 2021-12-25
# updated on 2022-01-07