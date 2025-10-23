from util import *



@apply
def apply(given):
    x, y = given.of(LessEqual)
    assert x.is_integer
    assert y.is_real

    return LessEqual(x, floor(y))


@prove
def prove(Eq):
    from Lemma import Algebra, Nat
    x = Symbol(integer=True, given=True)
    y = Symbol(real=True, given=True)

    Eq << apply(x <= y)

    Eq << ~Eq[1]

    Eq << Nat.Ge_Add_1.of.Gt.apply(Eq[-1])

    Eq << Algebra.Ge.of.Le.Ge.apply(Eq[0], Eq[-1])

    Eq << Eq[-1] - floor(y)

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Frac)

if __name__ == '__main__':
    run()



# created on 2018-05-22
