from util import *


@apply
def apply(is_negative, z):
    r = is_negative.of(Expr < 0)
    return Equal(Arg(r * z), Arg(-z))


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    z = Symbol(complex=True, given=True)
    r = Symbol(real=True)
    Eq << apply(r < 0, Arg(z))

    Eq << Algebra.Any.Eq.of.Lt_0.apply(Eq[0])

    Eq <<= Eq[1] & Eq[-1]

    Eq << Eq[-1].this.apply(Algebra.Cond.Any.given.Any.And, simplify=None)

    Eq << Eq[-1].this.expr.apply(Nat.Eq.UFn.given.Eq.UFn)





if __name__ == '__main__':
    run()
# created on 2020-01-18
# updated on 2023-08-26
