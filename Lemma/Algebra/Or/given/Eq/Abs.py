from util import *


@apply
def apply(imply):
    equal_positive, equal_negative = imply.of(Or)
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

    Eq << Eq[-1] ** 2

    Eq << Eq[-1] - Eq[-1].rhs

    Eq << Eq[-1].this.lhs.factor()

    Eq << Algebra.OrEqS_0.of.Mul.eq.Zero.apply(Eq[-1])

    Eq << Eq[-1].this.args[1] - x




if __name__ == '__main__':
    run()

# created on 2018-08-14
# updated on 2023-05-20
