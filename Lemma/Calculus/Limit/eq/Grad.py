from util import *


@apply
def apply(self, var=None):
    ((fx_epsilon, fx), ε), (S[ε], S[0]) = self.of(Limit[(Expr - Expr) / Symbol])
    if var is None:
        x, = fx.free_symbols
    else:
        x = var
    assert fx_epsilon == fx._subs(x, x + ε)
    return Equal(self, Derivative[x](fx), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Calculus

    x, ε = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Limit[ε:0]((f(x + ε) - f(x)) / ε))

    Eq << Eq[0].this.rhs.apply(Calculus.Grad.eq.Limit, ε)




if __name__ == '__main__':
    run()
# created on 2023-06-22
