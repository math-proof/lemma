from util import *



@apply
def apply(unequality, ne):
    lhs, rhs = ne.of(Unequal)
    factor = unequality.of(Unequal[0])
    return Unequal(lhs * factor, rhs * factor)


@prove
def prove(Eq):
    from Lemma import Algebra
    x, a, b = Symbol(real=True, given=True)
    Eq << apply(Unequal(x, 0), Unequal(a, b))

    Eq << ~Eq[-1]

    Eq << Algebra.EqDivS.of.Eq.apply(Eq[0], Eq[-1])

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()
# created on 2019-04-15
