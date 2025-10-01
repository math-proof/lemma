from util import *


def absorb_front(Sum, Equal, cond, cond_sum, criteria=None):
    fa, ga = cond.of(Equal)

    (fk, (k, a, b)), (gk, limit) = cond_sum.of(Equal[Sum[Tuple], Sum])

    assert k.is_integer
    assert limit == (k, a, b)

    assert fk._subs(k, a - 1) == fa
    assert gk._subs(k, a - 1) == ga

    if criteria:
        assert criteria(cond)
        assert criteria(cond_sum)

    return Equal(Sum[k:a - 1:b](fk), Sum[k:a - 1:b](gk))


@apply
def apply(*imply):
    return absorb_front(Sum, Equal, *imply)


@prove
def prove(Eq):
    from Lemma import Algebra

    k, a = Symbol(integer=True)
    b = Symbol(domain=Range(a + 1, oo))
    g, f = Function(integer=True)
    Eq << apply(Equal(g(a - 1), f(a - 1)), Equal(Sum[k:a:b](g(k)), Sum[k:a:b](f(k))))

    Eq << Algebra.EqAdd.of.Eq.Eq.apply(Eq[0], Eq[1])

    Eq << Eq[2].this.lhs.apply(Algebra.Sum.eq.AddSumS, cond={a - 1})

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.AddSumS, cond={a - 1})


if __name__ == '__main__':
    run()

# created on 2019-03-27
