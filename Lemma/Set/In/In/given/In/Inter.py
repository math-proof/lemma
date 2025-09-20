from util import *


@apply
def apply(contains1, contains2):
    e, A = contains1.of(Element)
    S[e], B = contains2.of(Element)

    return Element(e, A & B)


@prove
def prove(Eq):
    e = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    
    Eq << apply(Element(e, A), Element(e, B))
    
    Eq <<= Eq[0] & Eq[1]


if __name__ == '__main__':
    run()
# created on 2023-08-26
