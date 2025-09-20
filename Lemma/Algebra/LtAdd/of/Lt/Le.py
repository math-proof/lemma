from util import *



@apply
def apply(a_less_than_x, x_less_than_b):
    a, x = a_less_than_x.of(Less)
    b, y = x_less_than_b.of(LessEqual)

    return Less(a + b, x + y)


@prove
def prove(Eq):
    from Lemma import Algebra
    a, x, b, y = Symbol(real=True)

    Eq << apply(a < x, y <= b)

    Eq << Eq[0] + y

    Eq << Eq[1] + x

    Eq << Algebra.Lt.of.Lt.Le.apply(Eq[-2], Eq[-1])



if __name__ == '__main__':
    run()
# created on 2018-11-29
