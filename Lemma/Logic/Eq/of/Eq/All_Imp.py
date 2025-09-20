from util import *


@apply
def apply(f0, suffice, n=None, start=0):
    start = sympify(start)
    f0.of(Equal)
    fn, fn1 = suffice.of(Imply)
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, start) == f0
    assert n.domain.min() >= start

    return fn


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    n = Symbol(integer=True, nonnegative=True, given=False)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(Equal(f[0], g[0]), Imply(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])), n=n)

    h = Symbol(Stack[n](f[n] - g[n]))

    Eq << h[0].this.definition

    Eq.is_zero = Eq[-1].this.rhs.subs(Eq[0])

    Eq.suffice = Imply(Equal(h[n], 0), Equal(h[n + 1], 0), plausible=True)

    Eq << Eq.suffice.this.lhs.lhs.definition

    Eq << Eq[-1].this.lhs.reversed

    Eq << Eq[-1].this.rhs.lhs.definition

    Eq << Eq[-1].this.rhs.reversed

    Eq << Logic.Eq_0.of.Eq_0.All_Imp.apply(Eq.is_zero, Eq.suffice, n=n)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2018-04-17



