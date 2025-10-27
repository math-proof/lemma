from util import *



@apply
def apply(b_greater_than_x, x_greater_than_a):
    b, x = b_greater_than_x.of(Greater)
    S[x], a = x_greater_than_a.of(Greater)
    return Less(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat
    a, x, b = Symbol(real=True)

    Eq << apply(b > x, x > a)

    Eq << Nat.Gt.of.Gt.Gt.apply(Eq[0], Eq[1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-07-20

