from util import *


def simplify_negative_terms(cls, given):
    lhs, rhs = given.of(cls)

    if lhs.is_Add:
        lhs_args = lhs.args
    else:
        lhs_args = [lhs]

    rhs_positive, lhs_positive = std.array_split(lhs_args, lambda arg: arg._coeff_isneg())
    rhs_positive = (-arg for arg in rhs_positive)
    if rhs.is_Add:
        rhs_args = rhs.args
    else:
        rhs_args = [rhs]

    _lhs_positive, _rhs_positive = std.array_split(rhs_args, lambda arg: arg._coeff_isneg())
    _lhs_positive = (-arg for arg in _lhs_positive)

    return given.func(Add(*lhs_positive, *_lhs_positive), Add(*rhs_positive, *_rhs_positive))


@apply
def apply(given):
    return simplify_negative_terms(Equal, given)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x, y, a, b = Symbol(real=True, shape=(n,))

    Eq << apply(Equal(x - a, y - b))

    Eq << Eq[-1].this.lhs + a

    Eq << Eq[-1].this.lhs + b


if __name__ == '__main__':
    run()
# created on 2021-07-28
