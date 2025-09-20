from util import *
# given: x != y
# x not in {y}


@apply
def apply(given):
    x, S = given.of(Element)
    return Unequal(S, x.emptySet)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True, given=True)
    x = Symbol(complex=True, shape=(n,), given=True)
    S = Symbol(etype=dtype.complex[n], given=True)
    Eq << apply(Element(x, S))

    Eq << ~Eq[-1]

    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-09-22
