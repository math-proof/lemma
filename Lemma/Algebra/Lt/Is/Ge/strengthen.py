from util import *


@apply
def apply(lt):
    x, a = lt.of(Less)
    assert x.is_integer and a.is_integer
    return GreaterEqual(a, x + 1).simplify()


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Nat

    x, a = Symbol(integer=True, given=True)
    Eq << apply(x < a)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Nat.Le_Sub_1.of.Lt), Eq[-1].this.rhs.apply(Algebra.Lt.given.Le.strengthen)

    Eq <<= Eq[-2].this.lhs.reversed, Eq[-1].this.rhs.reversed

    Eq <<= Eq[-2].this.lhs + 1, Eq[-1].this.rhs + 1





if __name__ == '__main__':
    run()
# created on 2021-12-17
