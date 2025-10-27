from util import *



@apply
def apply(a_less_than_x, x_less_than_b):
    a, x = a_less_than_x.of(Greater)
    b, y = x_less_than_b.of(Greater)

    return Greater(a + b, x + y)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat
    a, x, b, y = Symbol(real=True)

    Eq << apply(a > x, y > b)

    Eq << Eq[0] + y

    Eq << Eq[1] + x

    Eq << Nat.Gt.of.Gt.Gt.apply(Eq[-2], Eq[-1])



if __name__ == '__main__':
    run()
# created on 2019-01-21
