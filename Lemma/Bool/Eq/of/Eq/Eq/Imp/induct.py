from util import *


@apply
def apply(f0, f1, suffice, n=None, start=0):
    start = sympify(start)
    f0.of(Equal)
    f1.of(Equal)
    fn, fn2 = suffice.of(Imply)
    assert fn._subs(n, n + 2) == fn2

    assert fn._subs(n, start) == f0
    assert fn._subs(n, start + 1) == f1
    assert n.domain.min() == start

    return fn


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n = Symbol(integer=True, positive=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Equal(f[1], g[1]), Equal(f[2], g[2]), Imply(Equal(f[n], g[n]), Equal(f[n + 2], g[n + 2])), n=n, start=1)

    m = Symbol(integer=True, nonnegative=True, given=False)
    h = Symbol(Stack[m](f[2 * m + 1] - g[2 * m + 1]))
    Eq << h[0].this.definition

    Eq.is_zero = Eq[-1].this.rhs.subs(Eq[0])

    Eq.suffice = Imply(Equal(h[m], 0), Equal(h[m + 1], 0), plausible=True)

    Eq << Eq.suffice.this.lhs.lhs.definition

    Eq << Eq[-1].this.lhs.reversed

    Eq << Eq[-1].this.rhs.lhs.definition

    Eq << Eq[-1].this.rhs.reversed

    Eq << Eq[2].subs(n, 2 * m + 1)

    Eq << Bool.Eq_0.of.Eq_0.All_Imp.apply(Eq.is_zero, Eq.suffice, n=m)

    Eq << Eq[-1].this.lhs.definition

    Eq.odd = Eq[-1].reversed

    h = Symbol("h'", Stack[m](f[2 * m + 2] - g[2 * m + 2]))
    Eq << h[0].this.definition

    Eq.is_zero_even = Eq[-1].this.rhs.subs(Eq[1])

    Eq.suffice_even = Imply(Equal(h[m], 0), Equal(h[m + 1], 0), plausible=True)

    Eq << Eq.suffice_even.this.lhs.lhs.definition

    Eq << Eq[-1].this.lhs.reversed

    Eq << Eq[-1].this.rhs.lhs.definition

    Eq << Eq[-1].this.rhs.reversed

    Eq << Eq[2].subs(n, 2 * m + 2)

    Eq << Bool.Eq_0.of.Eq_0.All_Imp.apply(Eq.is_zero_even, Eq.suffice_even, n=m)

    Eq << Eq[-1].this.lhs.definition

    Eq.even = Eq[-1].reversed

    Eq << Algebra.All.Eq.Limit_Eq_odd.of.Eq.apply(Eq.odd, m)

    Eq << Algebra.All.Eq.Limit_Eq_even.of.Eq.apply(Eq.even, m)

    Eq << Eq[-1].this.apply(Algebra.All.limits.subst.offset, -2)

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Eq[-1].subs(m, n)


if __name__ == '__main__':
    run()

# created on 2019-03-28
