from util import *


@apply
def apply(given, lhs=-1, rhs=None):
    from Lemma.Algebra.EqAdd.Is.Eq_Sub import transport
    return transport(Equal, given, lhs=lhs, rhs=rhs)


@prove
def prove(Eq):
    x, y, a = Symbol(real=True)
    Eq << apply(Equal(x + a, y))

    Eq << Eq[-1] + x


if __name__ == '__main__':
    run()
# created on 2022-04-01
