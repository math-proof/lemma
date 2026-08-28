from util import *


@apply(given=None)
def apply(x, b):
    assert x <= b
    return Iff(GreaterEqual(x, b), Equal(x, b))


@prove
def prove(Eq):
    from Lemma import Bool, Nat

    a = Symbol(integer=True)
    b = Symbol(integer=True, given=True)
    x = Symbol(domain=Range(a, b + 1), given=True)
    Eq << apply(x, b)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Nat.Eq.of.Ge.In_Icc)

    Eq << Eq[-1].this.lhs.apply(Nat.Ge.of.Eq)





if __name__ == '__main__':
    run()
# created on 2019-06-04
# updated on 2023-11-11

