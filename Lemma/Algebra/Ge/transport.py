from util import *


@apply
def apply(given, lhs=-1, rhs=None):
    from Lemma.Int.EqAdd.Is.Eq_Sub import transport
    return transport(GreaterEqual, given, lhs=lhs, rhs=rhs)


@prove
def prove(Eq):
    x, y, a = Symbol(real=True)
    Eq << apply(GreaterEqual(x + a, y))

    Eq << Eq[-1].this.rhs + x


if __name__ == '__main__':
    run()
# created on 2019-09-03
