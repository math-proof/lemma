from util import *



@apply
def apply(a_less_than_x, b_greater_than_x):
    a, x = a_less_than_x.of(LessEqual)
    b, _x = b_greater_than_x.of(Greater)
    if b == a:
        a, x, b, _x = _x, a, x, b
    assert x == _x
    return Greater(b, a)


@prove
def prove(Eq):
    from Lemma import Algebra
    a, x, b = Symbol(real=True)

    Eq << apply(a <= x, b > x)

    Eq << Eq[1].reversed

    Eq << Algebra.Lt.of.Le.Lt.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-07-29

