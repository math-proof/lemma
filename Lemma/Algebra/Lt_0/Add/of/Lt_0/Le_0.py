from util import *


@apply
def apply(is_negative, is_nonpositive):
    a = is_negative.of(Expr < 0)
    y = is_nonpositive.of(Expr <= 0)

    return Less(a + y, 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, y = Symbol(real=True)
    Eq << apply(y < 0, a <= 0)

    Eq << Algebra.LtAdd.of.Lt.Le.apply(Eq[0], Eq[1])


if __name__ == '__main__':
    run()
# created on 2018-11-29
