from util import *


@apply
def apply(given):
    e, s = given.of(Element[FiniteSet])
    return Equal(e, s)


@prove
def prove(Eq):
    e, a = Symbol(integer=True, given=True)
    Eq << apply(Element(e, {a}))

    Eq << Eq[0].simplify()




if __name__ == '__main__':
    run()
# created on 2023-04-18
from . import In_Finset
