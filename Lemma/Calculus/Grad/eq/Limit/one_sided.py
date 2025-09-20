from util import *


@apply
def apply(self, var=None):
    fx, (x, S[1]) = self.of(Derivative)
    x, epsilon = x.clear_infinitesimal()
    assert epsilon.is_infinitesimal
    if var is None:
        var = self.generate_var(var='epsilon', real=True)

    assert not self._has(var)

    return Equal(self, Limit[var:epsilon]((fx._subs(x, x + var) - fx) / var))


@prove(provable=False)
def prove(Eq):
    x, epsilon = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Derivative[x + S.Infinitesimal](f(x)), var=epsilon)


if __name__ == '__main__':
    run()
# created on 2023-10-15
