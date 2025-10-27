from util import *


@apply
def apply(fraction):
    x = fraction.of(FractionalPart)
    x = -x
    x = x.of(Expr / 2)

    return Equal(fraction, frac(x / 2))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Nat

    n = Symbol(integer=True)
    Eq << apply(frac(-n / 2))

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[0], cond=Equal(n % 2, 0))

    Eq <<= Bool.Imp.given.Imp_And.apply(Eq[-2]), Bool.Imp.given.Imp_And.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.find(Equal[0]).apply(Algebra.Eq_even.given.Any), Eq[-1].this.rhs.find(Unequal[0]).apply(Algebra.Mod.ne.Zero.given.Any)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Cond.Any.given.Any.And, simplify=None), Eq[-1].this.rhs.apply(Algebra.Cond.Any.given.Any.And, simplify=None)

    Eq <<= Eq[-2].this.find(And).apply(Nat.Eq.UFn.given.Eq.UFn), Eq[-1].this.find(And).apply(Nat.Eq.UFn.given.Eq.UFn)

    Eq << Eq[-2].this.lhs.apply(Algebra.Any.of.Eq_even)

    Eq << Eq[-1].this.lhs.apply(Algebra.Any.of.Mod.ne.Zero)





if __name__ == '__main__':
    run()
# created on 2019-05-10
# updated on 2023-08-26
