from util import *



# given e not in S
@apply
def apply(given):
    e, S = given.of(NotElement)
    S = S.of(Intersection)
    return Or(*(NotElement(e, s) for s in S))


@prove
def prove(Eq):
    e = Symbol(integer=True, given=True)
    B, A = Symbol(etype=dtype.integer, given=True)

    Eq << apply(NotElement(e, A & B))

    Eq << ~Eq[-1]

    Eq << Eq[-1].simplify()

    Eq << ~Eq[-1]

if __name__ == '__main__':
    run()

# created on 2021-08-21
