from util import *


@apply
def apply(self, *, simplify=True):
    function, *limits_d = self.of(Integral)
    f, *limits_s = function.of(Derivative)

    f = Integral(f, *limits_d)
    if simplify:
        f = f.simplify()
    return Equal(self, Derivative(f, *limits_s))


@prove(proved=False)
def prove(Eq):
    x, y = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Integral[x](Derivative[y](f(x, y))))


if __name__ == '__main__':
    run()
# created on 2023-03-26
