from util import *


@apply
def apply(is_nonzero, given, x):
    a = is_nonzero.of(Unequal[0])
    fx = given.of(Equal[0])
    assert fx._has(x)
    if x.is_Symbol:
        x_ = x
    else:
        x, x_ = Dummy('x', **x.type.dict), x
        fx = fx._subs(x_, x)

    p = fx.as_poly(x)
    assert p.degree() == 1
    S[a] = p.nth(1)
    b = p.nth(0)
    return Equal(x_, -b / a)


@prove
def prove(Eq):
    from Lemma import Nat, Int

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(Unequal(a, 0), Equal(a * x + b, 0), x=x)

    Eq << Eq[1].this.apply(Int.EqAdd.Is.Eq_Sub, lhs=0)

    Eq << Nat.Div.of.Eq.nonzero.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-08-16
# updated on 2026-08-22
