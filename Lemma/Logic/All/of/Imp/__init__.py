from util import *


@apply
def apply(given, wrt=None):
    cond, q = given.of(Imply)
    if wrt is None:
        wrt = cond.wrt
    elif isinstance(wrt, tuple):
        eqs = cond.of(And)
        assert len(eqs) == len(wrt)
        limits = []
        wrt = {*wrt}
        for eq in eqs:
            x, = eq.free_symbols & wrt
            limits.append((x, eq))
        return All(q, *limits)
    return All[wrt:cond](q)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    a, b, x, y = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Imply((f(a) > x) & (f(b) > y), f(a, b) > g(x, y)), wrt=(a, b))

    Eq << Eq[0].this.apply(Logic.Imp.fold, index=1)

    Eq << Logic.All.of.Imp.single_variable.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Logic.All.of.Imp.single_variable)


if __name__ == '__main__':
    run()

# created on 2019-09-02

from . import single_variable
