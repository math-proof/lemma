from util import *


@apply
def apply(is_negative, is_negative1):
    a = is_negative.of(Expr < 0)
    y = is_negative1.of(Expr < 0)

    return Less(a + y, 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, y = Symbol(real=True)
    Eq << apply(y < 0, a < 0)

    Eq << Algebra.LtAdd.of.Lt.Lt.apply(Eq[1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2020-01-23
