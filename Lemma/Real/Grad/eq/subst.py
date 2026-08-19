from util import *


@apply
def apply(self, old, new):
    assert self.is_Derivative
    assert self._has(new)
    return Equal(self, Subs[old:new](self._subs(new, old)))


@prove
def prove(Eq):
    x, t = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Derivative(f(t), t), x, t)

    Eq << Eq[-1].this.rhs.doit()


if __name__ == '__main__':
    run()
# created on 2021-09-28
