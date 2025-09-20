from util import *


@apply
def apply(le):
    abs_x, a = le.of(LessEqual)
    x = abs_x.of(Abs)
    assert x.is_extended_real
    return LessEqual(x, a), GreaterEqual(x, -a)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a = Symbol(integer=True, given=True)
    Eq << apply(abs(x) <= a)

    Eq << Algebra.Le.of.LeAbs.apply(Eq[0])

    Eq << -Algebra.Le.of.LeAbs.apply(Eq[0], negate=True)





if __name__ == '__main__':
    run()
# created on 2018-07-30
# updated on 2023-04-16
