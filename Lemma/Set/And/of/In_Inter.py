from util import *


@apply
def apply(given, index=-1):
    e, args = given.of(Element[Intersection])
    first = Intersection(*args[:index])
    second = Intersection(*args[index:])
    return Element(e, first), Element(e, second)


@prove
def prove(Eq):
    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A & B))

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()

# created on 2018-09-07


