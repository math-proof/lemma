from util import *


@apply(simplify=False)
def apply(given, index=None):
    fx, fy = given.of(Imply)
    if index is None:
        cond = fx
    else:
        eqs = fx.of(And)
        cond = eqs[index]
        if isinstance(index, slice):
            cond = And(*cond)

    return Imply(fx, cond & fy)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n = Symbol(integer=True, nonnegative=True)
    A = Symbol(etype=dtype.integer)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Imply(Equal(f[n], g[n]) & Element(n, A), Equal(f[n + 1], g[n + 1])), index=0)

    Eq << Imply(Equal(f[n], g[n]) & Element(n, A), Equal(f[n], g[n]), plausible=True)

    Eq << Logic.ImpAndS.of.Imp.Imp.apply(Eq[0], Eq[-1], simplify=False)


if __name__ == '__main__':
    run()
# created on 2018-02-02

