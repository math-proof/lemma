from util import *



@apply
def apply(a_less_than_x, b_eq_x):
    a, x = a_less_than_x.of(Less)
    b, S[x] = b_eq_x.of(Equal)
    return Greater(b, a)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat
    a, x, b = Symbol(real=True)

    Eq << apply(a < x, Equal(b, x))

    Eq << Eq[0] + Eq[1].reversed

    Eq << Eq[-1].reversed

    Eq << Eq[-1].this.apply(Nat.GtAddS.Is.Gt)


if __name__ == '__main__':
    run()
# created on 2019-12-12

