from util import *


@apply
def apply(self):
    fx, (x, x0) = self.of(Limit)
    x0, dir = x0.clear_infinitesimal()
    assert fx.is_continuous_at(x0)
    return Equal(self, fx._subs(x, x0))


@prove(provable=False)
def prove(Eq):
    f = Function(real=True, continuous=True)
    x, x0 = Symbol(real=True)
    Eq << apply(Limit[x:x0](f(x)))


if __name__ == '__main__':
    run()
# created on 2020-05-01
