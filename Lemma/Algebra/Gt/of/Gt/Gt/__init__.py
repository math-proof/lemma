from util import *



@apply
def apply(b_greater_than_x, x_greater_than_a):
    b, x = b_greater_than_x.of(Greater)
    _x, a = x_greater_than_a.of(Greater)
    if b == a:
        b, x, _x, a = _x, a, b, x
    assert x == _x
    return Greater(b, a)


@prove
def prove(Eq):
    from Lemma import Algebra
    a, x, b = Symbol(real=True)

    Eq << apply(b > x, x > a)

    Eq << Eq[0] + Eq[1]

    Eq << Eq[-1].this.apply(Algebra.Gt.simp.common_terms)


if __name__ == '__main__':
    run()
# created on 2018-05-19

from . import subst
