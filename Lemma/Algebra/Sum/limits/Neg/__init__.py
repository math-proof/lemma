from util import *


@apply
def apply(self):
    expr, (i,_a, a1) = self.of(Sum)
    a = a1 - 1
    assert _a == -a
    return Equal(self, Sum[i:-a:a + 1](expr._subs(i, -i)), evaluate=False)


@prove
def prove(Eq):
    i = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    f = Function(real=True)
    Eq << apply(Sum[i:-n:n + 1](f(i)))

    Eq << Eq[-1] - Eq[-1].rhs


if __name__ == '__main__':
    run()
# created on 2020-03-15
from . import Infty
