from util import *



@apply
def apply(a_less_than_x, x_less_than_b):
    a, x = a_less_than_x.of(Less)
    _x, b = x_less_than_b.of(Less)
    if b == a:
        a, x, S[x], b = _x, b, a, x
    return Less(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra
    a, x, b = Symbol(real=True)

    Eq << apply(a < x, x < b)

    Eq << Eq[0] + Eq[1]

    Eq << Eq[-1].this.apply(Algebra.LtAddS.Is.Lt)

if __name__ == '__main__':
    run()
# created on 2018-10-11

from . import subst
