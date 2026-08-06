from util import *


@apply
def apply(self):
    f, (m, domain) = self.of(Sum)
    n, expr, base_set = domain.image_set()

    assert not (expr / n)._has(n)
    f = f._subs(m, expr)

    return Equal(self, self.func(f, (n, base_set)))


@prove(proved=False)
def prove(Eq):
    n, a = Symbol(integer=True)
    f = Symbol(shape=(oo,), real=True)
    h = Function(real=True)
    t = Function(integer=True)
    Eq << apply(Sum[n:imageset(n, a * n, h(n) > 0)](f[n]))














if __name__ == '__main__':
    run()
# created on 2018-05-01
