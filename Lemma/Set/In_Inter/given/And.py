from util import *


@apply
def apply(imply, index=-1):
    x, args = imply.of(Element[Intersection])
    first = Intersection(*args[:index])
    second = Intersection(*args[index:])

    return Element(x, first), Element(x, second)


@prove
def prove(Eq):
    x = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(x, A & B))

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()

# created on 2021-04-25


