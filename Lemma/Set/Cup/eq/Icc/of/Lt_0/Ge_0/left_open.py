from util import *


@apply
def apply(is_negative, is_nonnegative, k=None):
    a = is_negative.of(Expr < 0)
    b = is_nonnegative.of(Expr >= 0)

    assert a.is_integer and b.is_integer
    if k is None:
        k = a.generate_var(b.free_symbols, integer=True)
    return Equal(Cup[k:a:b](Interval(k, k + 1, left_open=True)), Interval(a, b, left_open=True))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, k = Symbol(integer=True)
    Eq << apply(a < 0, b >= 0, k)

    Eq << Set.Cup.eq.UnionCupS.apply(Cup[k:a:b](Eq[-1].lhs.expr), cond=Range(a, 0))

    Eq <<= Algebra.EqMax.of.Lt.apply(Eq[0]), Algebra.EqMin.of.Ge.apply(Eq[1])

    Eq <<= Eq[-3].rhs.args[1].this.subs(Eq[-2]), Eq[-3].rhs.args[0].this.subs(Eq[-1])

    Eq <<= Set.Cup_Ioc.eq.Ioc0.of.Ge_0.apply(Eq[1], k), Set.Cup_Ioc.eq.Ioc_0.of.Lt_0.apply(Eq[0], k)

    Eq <<= Eq[-4].subs(Eq[-2]), Eq[-3].subs(Eq[-1])

    Eq << Eq[3].subs(Eq[-1], Eq[-2])

    Eq << Set.Union.eq.Icc.of.Lt.Le.apply(Eq[0], Eq[1].reversed, left_open=True)

    Eq << Eq[-2].subs(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2018-10-13
# updated on 2023-05-20
