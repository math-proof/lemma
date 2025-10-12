from util import *


@apply
def apply(x):
    return log(x) <= x - 1


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Nat, Nat

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << Eq[0] - x

    Eq << Algebra.Cond.given.All.domain_defined.apply(Eq[-1])

    Eq << Algebra.All.given.And.All.apply(Eq[-1], cond=x >= 1)

    x0 = Symbol(domain=Interval(0, 1, left_open=True, right_open=True))
    x1 = Symbol(domain=Interval(1, oo))
    Eq <<= Algebra.All.given.Cond.subst.apply(Eq[-1], x, x0), Algebra.All.given.Cond.subst.apply(Eq[-2], x, x1)

    Eq.is_positive, Eq.is_nonpositive = Greater(Derivative[x0](Eq[-2].lhs), 0, plausible=True), LessEqual(Derivative[x1](Eq[-1].lhs), 0, plausible=True)

    Eq << Eq.is_positive.this.lhs.doit()

    Eq << Eq.is_nonpositive.this.lhs.doit()

    Eq <<= Eq[-2] * x0, Eq[-1] * x1

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS), Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Calculus.Lt.of.Gt_0.monotony.apply(Eq.is_positive)

    Eq << Nat.Le.of.Lt.apply(Eq[-1])

    Eq << Calculus.Le.of.Le_0.monotony.apply(Eq.is_nonpositive)




if __name__ == '__main__':
    run()
# created on 2019-09-21
# updated on 2023-05-14
