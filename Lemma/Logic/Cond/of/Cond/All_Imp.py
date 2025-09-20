from util import *


@apply
def apply(f0, suffice, n=None, start=0):
    start = sympify(start)
    fn, fn1 = suffice.of(Imply)
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, start) == f0
    a = n.domain.min()
    if a == start:
        return fn
    if a < start:
        diff = start - a
        if diff.is_Number:
            for i in range(diff):
                if fn._subs(n, a + i):
                    continue
                return
            return fn


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(LessEqual(f[0], g[0]), Imply(LessEqual(f[n], g[n]), LessEqual(f[n + 1], g[n + 1])), n=n)

    h = Symbol(Stack[n](Bool(f[n] <= g[n])))

    Eq << h[0].this.definition

    Eq << Logic.Bool.eq.One.of.Cond.apply(Eq[0])

    Eq.initial = Logic.Eq.of.Eq.Eq.apply(Eq[-2], Eq[-1])

    Eq.suffice = Imply(Equal(h[n], 1), Equal(h[n + 1], 1), plausible=True)

    Eq << Eq.suffice.this.lhs.lhs.definition

    Eq << Eq[-1].this.lhs.lhs.apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].this.rhs.lhs.definition

    Eq << Eq[-1].this.rhs.lhs.apply(Logic.Bool.eq.Ite)

    Eq << Logic.Eq.of.Eq.All_Imp.apply(Eq.initial, Eq.suffice, n=n)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.lhs.apply(Logic.Bool.eq.Ite)


if __name__ == '__main__':
    run()

# created on 2018-04-18

