from util import *


@apply
def apply(cond, cond_sum):
    fa, ga = cond.of(Equal)

    (fk, (k, a, b)), (gk, _limit) = cond_sum.of(Equal[Cup, Cup])

    assert fk._subs(k, a - 1) == fa
    assert _limit == (k, a, b)
    assert gk._subs(k, a - 1) == ga

    return Equal(Cup[k:a - 1:b](fk), Cup[k:a - 1:b](gk))


@prove
def prove(Eq):
    from Lemma import Set
    k, a = Symbol(integer=True)
    b = Symbol(domain=Range(a + 1, oo))
    g, f = Function(etype=dtype.integer)

    Eq << apply(Equal(g(a - 1), f(a - 1)), Equal(Cup[k:a:b](g(k)), Cup[k:a:b](f(k))))

    Eq << Set.EqUnionS.of.Eq.Eq.apply(Eq[0], Eq[1])

#     Eq << Eq[2].this.lhs.bisect({a - 1})

#     Eq << Eq[-1].this.rhs.bisect({a - 1})


if __name__ == '__main__':
    run()

# created on 2021-03-28
