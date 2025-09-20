from util import *



@apply
def apply(a_less_than_x, x_less_than_b):
    a, x = a_less_than_x.of(Greater)
    b, y = x_less_than_b.of(GreaterEqual)

    return Greater(a + b, x + y)


@prove
def prove(Eq):
    from Lemma import Algebra
    a, x, b, y = Symbol(real=True)

    Eq << apply(a > x, y >= b)

    Eq << Eq[0] + y

    Eq << Eq[1] + x

    Eq << Algebra.Gt.of.Gt.Ge.apply(Eq[-2], Eq[-1])



if __name__ == '__main__':
    run()
# created on 2019-01-04
