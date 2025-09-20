from util import *



@apply
def apply(f0, suffice, n=None, x=None, start=0, return_hypothesis=True):
    start = sympify(start)
    f0.of(Equal)
    fn, fn1 = suffice.of(Imply)

    x_wild = Wild('x', **x.type.dict)
    fn_hypothesis = fn
    fn = fn._subs(x, x_wild)

    x_, *_ = fn1._subs(n, n - 1).match(fn).values()

    x0_, *_ = f0.match(fn._subs(n, start)).values()

    assert n.domain.min() == start

    fn = fn._subs(x_wild, x_)
    if return_hypothesis:
        return fn, fn_hypothesis
    return fn


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    n = Symbol(integer=True, nonnegative=True)
    f, g = Function(shape=(), real=True)
    x, y, z = Symbol(real=True)

    Eq << apply(Equal(f[0](z), g[0](z)), Imply(Equal(f[n](x), g[n](x)), Equal(f[n + 1](y), g[n + 1](y))), n=n, x=x)

    Eq << Eq[0].subs(z, y)

    Eq << Eq[1].subs(x, y)

    Eq << Logic.Cond.of.Cond.All_Imp.apply(Eq[-2], Eq[-1], n=n)

    Eq << Eq[2].subs(y, x)


if __name__ == '__main__':
    run()
# created on 2019-04-17
