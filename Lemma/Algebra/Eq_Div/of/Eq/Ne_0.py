from util import *



@apply
def apply(unequality, equality):
    divisor = unequality.of(Unequal[0])
    lhs, rhs = equality.of(Equal)
    return Equal(lhs / divisor, rhs / divisor)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic, Logic
    x, a, b = Symbol(real=True)
    Eq << apply(Unequal(x, 0), Equal(x * a, b))

    Eq << Eq[1] / x
    Eq <<= Eq[-1] & Eq[0]

    Eq << Logic.And_And.of.And.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-08-13
