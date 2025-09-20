from util import *


def all_getitem(given, cls, var=None):
    lhs, rhs = given.of(cls)

    if var is None:
        var = given.generate_var(integer=True)

    if len(lhs.shape) > len(rhs.shape):
        n = lhs.shape[0]
        lhs = lhs[var]
    elif len(lhs.shape) < len(rhs.shape):
        n = rhs.shape[0]
        rhs = rhs[var]
    else:
        n = lhs.shape[0]
        lhs = lhs[var]
        rhs = rhs[var]

    return All[var:n](cls(lhs, rhs))

@apply
def apply(le, var=None):
    return all_getitem(le, LessEqual, var=var)

@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True)
    Eq << apply(x <= y)

    Eq << Eq[0].this.apply(Algebra.Le.Is.All.Le)


if __name__ == '__main__':
    run()
# created on 2022-03-31
