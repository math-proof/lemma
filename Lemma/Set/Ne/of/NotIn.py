from util import *



# given e not in S
@apply
def apply(given, index=0):
    e, s = given.of(NotElement)
    s = s.of(FiniteSet)
    return Unequal(e, s[index])


@prove
def prove(Eq):
    e, a, b = Symbol(integer=True, given=True)

    Eq << apply(NotElement(e, {a, b}))

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2018-11-16
