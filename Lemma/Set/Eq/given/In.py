from util import *


# given : A & B = A | B => A = B


@apply(simplify=False)
def apply(given):
    x, a = given.of(Equal)
    return Element(x, a.set)


@prove
def prove(Eq):
    x, a = Symbol(real=True)

    Eq << apply(Equal(x, a))

    Eq << Eq[1].simplify()



if __name__ == '__main__':
    run()

# created on 2020-04-17
