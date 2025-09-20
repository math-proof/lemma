from util import *



@apply
def apply(notcontains1, notcontains2):
    e, A = notcontains1.of(NotElement)
    S[e], B = notcontains2.of(NotElement)

    return NotElement(e, (A | B).simplify())


@prove
def prove(Eq):
    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)

    Eq << apply(NotElement(e, A), NotElement(e, B))

    Eq <<= Eq[0] & Eq[1]


if __name__ == '__main__':
    run()

# created on 2018-03-09
