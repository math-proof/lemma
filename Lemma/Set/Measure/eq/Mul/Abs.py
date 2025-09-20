from util import *


@apply
def apply(self):
    fx, (x, S) = self.of(Measure[Cup[FiniteSet]])
    f, coeff = std.array_split(fx.of(Mul), lambda arg: arg._has(x))
    f = Mul(*f)
    coeff = Mul(*coeff)
    shape = fx.shape
    if shape:
        if len(shape) == 1:
            m, = shape
            if coeff.shape:
                if len(coeff.shape) == 1:
                    n, = coeff.shape
                    scale = Product[i:n](abs(coeff[i])).doit()
                else:
                    ...
            else:
                scale = abs(coeff) ** m
        else:
            ...
    else:
        if coeff.shape:
            if len(coeff.shape) == 1:
                n, = coeff.shape
                scale = Product[i:n](abs(coeff[i])).doit()
            else:
                ...
        else:
            scale = abs(coeff)

    return Equal(self, scale * Measure(imageset(x, f, S)))


@prove(proved=False)
def prove(Eq):
    x, h = Symbol(real=True)
    f = Function(real=True)
    S = Symbol(etype=dtype.real)
    Eq << apply(Measure(imageset(x, f(x) * h, S)))


if __name__ == '__main__':
    run()
# created on 2021-09-07
