from util import *


def simplify_common_terms(cls, given):
    lhs, rhs = given.of(cls)

    if lhs.is_Add:
        lhs_args = lhs.args
    else:
        lhs_args = [lhs]

    if rhs.is_Add:
        rhs_args = rhs.args
    else:
        rhs_args = [rhs]

    common_terms = {*lhs_args} & {*rhs_args}
    assert common_terms
    lhs = {*lhs_args} - common_terms
    rhs = {*rhs_args} - common_terms

    return given.func(Add(*lhs), Add(*rhs))

@apply
def apply(given):
    return simplify_common_terms(Equal, given)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x, y, a = Symbol(real=True, shape=(n,))


    Eq << apply(Equal(x + a, y + a))

    Eq << Eq[-1].this.lhs - a


if __name__ == '__main__':
    run()
# created on 2018-03-22
