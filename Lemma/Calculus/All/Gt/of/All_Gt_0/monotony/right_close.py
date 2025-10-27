from util import *


@apply
def apply(given):
    (fx, (x, S[1])), (S[x], domain) = given.of(All[Derivative > 0])
    a, b = domain.of(Interval)
    assert domain.is_closed
    return All[x:Interval(a, b, left_open=True)](Greater(fx, fx._subs(x, a)))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Calculus, Bool, Nat

    a, b, x = Symbol(real=True)
    domain = Interval(a, b)
    f = Function(real=True)
    Eq << apply(All[x:domain](Derivative[x](f(x)) > 0))

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[1], cond=a < b)

    Eq << Eq[-1].this.rhs.apply(Algebra.All.given.All.And.limits_cond, simplify=None)

    Eq << (a >= b).this.apply(Set.Eq_Empty.Icc.of.Ge, left_open=True)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Nat.Eq.UFn.given.Eq.UFn)

    Eq << Bool.Imp.of.Cond.apply(Eq[0], cond=a < b)

    Eq << Bool.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Calculus.All.Gt.of.Lt.All_Gt_0.monotony.right_close)




if __name__ == '__main__':
    run()
# created on 2020-04-23
# updated on 2023-08-26
