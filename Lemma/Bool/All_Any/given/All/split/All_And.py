from util import *


@apply
def apply(given):
    et, *limits = given.of(All[And])
    return tuple(All(eq, *limits) for eq in et)


@prove
def prove(Eq):
    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,), given=True)

    A = Symbol(etype=dtype.real[k])

    f, g = Function(real=True)
    b = Symbol(shape=(k,), real=True)

    Eq << apply(All[x:A](And(Unequal(x, y), Unequal(f(x), g(y)), Equal(f(x), b))))

    Eq <<= Eq[1] & Eq[2] & Eq[3]


if __name__ == '__main__':
    run()

# created on 2021-08-25
