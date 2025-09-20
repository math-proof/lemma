from util import *


@apply
def apply(fraction):
    x = fraction.of(FractionalPart)

    return Equal(fraction, x - floor(x))


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(frac(x))


if __name__ == '__main__':
    run()
# created on 2018-05-06
