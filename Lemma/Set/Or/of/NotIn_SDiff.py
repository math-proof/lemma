from util import *



# given e not in S
@apply
def apply(given, simplify=True):
    e, S = given.of(NotElement)
    U, A = S.of(Complement)
    contains = Element(e, A)
    notcontains = NotElement(e, U)
    if simplify:
        contains = contains.simplify()
        notcontains = notcontains.simplify()

    return Or(notcontains, contains)


@prove
def prove(Eq):
    e = Symbol(integer=True, given=True)
    U, A = Symbol(etype=dtype.integer, given=True)

    Eq << apply(NotElement(e, Complement(U, A)))

    Eq << ~Eq[1]

    Eq << Eq[-1].simplify()

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2020-10-01
