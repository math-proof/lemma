from util import *


@apply
def apply(given):
    (x, B), (S[x], A) = given.of(Any[Element])
    return Any[x:B](Element(x, A))


@prove
def prove(Eq):

    A, B = Symbol(etype=dtype.real)
    e = Symbol(real=True)

    Eq << apply(Any[e:A](Element(e, B)))

    Eq << Eq[-1].simplify()

    Eq << Eq[0].simplify()


if __name__ == '__main__':
    run()

# created on 2020-09-04
