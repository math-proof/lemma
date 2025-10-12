from util import *


@apply
def apply(given, lhs=0, rhs=None):
    LHS, RHS = given.of(Equal)
    assert LHS.is_nonzero or RHS.is_nonzero
    if lhs is not None:
        if LHS.is_Mul:
            divisor = LHS.args[lhs]

    else:
        if RHS.is_Mul:
            divisor = RHS.args[rhs]

    return Equal(LHS / divisor, RHS / divisor)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x, y = Symbol(real=True)
    d = Symbol(real=True, zero=False)
    Eq << apply(Equal(x * y, d))

    Eq << Unequal(d, 0, plausible=True)

    Eq << Eq[-1].subs(Eq[0].reversed)

    Eq << Algebra.Ne_0.Ne_0.of.Mul.ne.Zero.apply(Eq[-1])

    Eq << Algebra.Inv.ne.Zero.of.Ne_0.apply(Eq[-2])

    Eq << Nat.EqMulS.of.Eq.apply(Eq[-1], Eq[0])



if __name__ == '__main__':
    run()
# created on 2021-11-09
