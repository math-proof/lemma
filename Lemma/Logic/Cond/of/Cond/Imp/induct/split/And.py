from util import *


@apply
def apply(f0, suffice, n=None, x=None, start=0, hypothesis=True):
    start = sympify(start)
    fn_and_fnt, fn1 = suffice.of(Imply)

    fn, fnt = fn_and_fnt.of(And)

    if fn1._subs(n, n - 1) == fnt:
        fn, fnt = fnt, fn

    assert fn1._subs(n, n - 1) == fn

    x_wild = Wild('x', **x.type.dict)

    fn_ = fn._subs(x, x_wild)

    x_t, *_ = fnt.match(fn_).values()

    assert fn._subs(n, start) == f0

    assert n.domain.min() == start

    return fn


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n = Symbol(integer=True, nonnegative=True)
    f, g, t = Function(shape=(), real=True)
    x = Symbol(real=True)
    Eq << apply(f[0](x) > g[0](x), Imply((f[n](x) > g[n](x)) & (f[n](t(x)) > g[n](t(x))), (f[n + 1](x) > g[n + 1](x))), n=n, x=x)

    Eq << Eq[2].cond.this.apply(Algebra.Cond.of.Cond.subst, x, t(x))

    Eq << Logic.Imp_And.of.ImpAnd.apply(Eq[-1])
    Eq.induct = Logic.Imp.of.Imp.Imp.apply(Eq[-1], Eq[1])
    Eq << Logic.Cond.of.Cond.All_Imp.apply(Eq[0], Eq.induct, n=n)




if __name__ == '__main__':
    run()
# created on 2019-03-21
# updated on 2023-05-21
