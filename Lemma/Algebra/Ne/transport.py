from util import *


@apply
def apply(given, lhs=-1, rhs=None):
    from Lemma.Algebra.Eq.transport import transport
    return transport(Unequal, given, lhs=lhs, rhs=rhs)


@prove
def prove(Eq):
    x, y, a = Symbol(real=True)
    Eq << apply(Unequal(x + a, y))

    Eq << Eq[-1].this.rhs + x


if __name__ == '__main__':
    run()
# created on 2021-08-21
