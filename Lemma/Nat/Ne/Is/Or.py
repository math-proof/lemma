from util import *


@apply
def apply(given):
    x, y = given.of(Unequal)
    assert x.is_real and y.is_real
    return Or(x > y, x < y, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Bool, Nat

    x, y = Symbol(real=True, given=True)
    Eq << apply(Unequal(x, y))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Bool.Or.of.Ne)

    Eq << Eq[-1].this.rhs.apply(Nat.Ne.given.Or)




if __name__ == '__main__':
    run()
# created on 2023-04-19
