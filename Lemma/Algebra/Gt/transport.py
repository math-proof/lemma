from util import *


@apply
def apply(given, lhs=-1, rhs=None):
    from Lemma.Algebra.Eq.transport import transport
    return transport(Greater, given, lhs=lhs, rhs=rhs)


@prove
def prove(Eq):
    a, x, y = Symbol(real=True)
    Eq << apply(Greater(x + a, y))

    Eq << Eq[-1].this.rhs + x


if __name__ == '__main__':
    run()
# created on 2019-06-13
