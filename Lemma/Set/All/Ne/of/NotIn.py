from util import *



@apply
def apply(given, reverse=False):
    e, S = given.of(NotElement)

    x = given.generate_var(**e.type.dict)
    if reverse:
        return All[x:S](Unequal(x, e))
    return All[x:S](Unequal(e, x))


@prove
def prove(Eq):
    x = Symbol(integer=True, given=True)

    S = Symbol(etype=dtype.integer, given=True)

    Eq << apply(NotElement(x, S))

    Eq << ~Eq[1]

    Eq << Eq[-1].simplify()

    Eq <<= Eq[-1] & Eq[0]

if __name__ == '__main__':
    run()

# created on 2021-01-13
