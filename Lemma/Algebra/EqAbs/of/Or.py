from util import *


@apply
def apply(given):
    equal_positive, equal_negative = given.of(Or)
    y, x = equal_positive.of(Equal)
    _y, _x = equal_negative.of(Equal)
    if y != _y:
        S[y], _x = _x, _y

    assert x == -_x

    return Equal(abs(y), abs(x))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(Equal(y, x) | Equal(y, -x))

    Eq << Eq[0].this.args[0].apply(Algebra.EqAbs.of.Eq)

    Eq << Eq[-1].this.args[0].apply(Algebra.EqAbs.of.Eq)


if __name__ == '__main__':
    run()

# created on 2018-08-14
