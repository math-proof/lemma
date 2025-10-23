from util import *


@apply
def apply(given, x):
    fx = given.of(Equal[0])
    assert fx._has(x)
    if x.is_Symbol:
        x_ = x
    else:
        x, x_ = Dummy('x', **x.type.dict), x
        fx = fx._subs(x_, x)

    p = fx.as_poly(x)
    assert p.degree() == 1
    a = p.nth(1)
    b = p.nth(0)
    return Imply(Equal(a, 0), Equal(b, 0)), Imply(Unequal(a, 0), Equal(x_, -b / a))

@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Nat, Int

    x, a, b = Symbol(real=True)
    Eq << apply(Equal(a * x + b, 0), x=x)

    Eq << Bool.And.Imp.of.Cond.split.apply(Eq[0], cond=Equal(a, 0))

    Eq <<= Bool.Imp_And.of.ImpAnd.apply(Eq[-2]), Eq[-1].this.rhs.apply(Int.EqAdd.Is.Eq_Sub, lhs=0)

    Eq <<= Eq[-2].this.rhs.apply(Bool.Cond.of.Eq.Cond.subst), Bool.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Nat.EqDivS.of.Eq)


if __name__ == '__main__':
    run()
# created on 2018-08-16
