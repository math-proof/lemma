from util import *


@apply
def apply(self):
    fx, (x, a, b) = self.of(Integral)

    return Equal(self, -Integral[x:b:a](fx), evaluate=False)


@prove(provable=False)
def prove(Eq):
    x, a, b = Symbol(real=True)
    f = Function(real=True, integrable=True)
    Eq << apply(Integral[x:a:b](f(x)))


if __name__ == '__main__':
    run()
# created on 2020-05-23
