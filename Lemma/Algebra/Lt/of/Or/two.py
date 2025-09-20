from util import *


@apply
def apply(given, wrt=None):
    from Lemma.Logic.BFnIte.of.OrAndS import expr_cond_pair
    or_eqs = given.of(Or)
    assert len(or_eqs) == 2
    return Less(Piecewise(*expr_cond_pair(Less, or_eqs, wrt, reverse=True)).simplify(), wrt)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, p = Symbol(real=True, given=True)
    A = Symbol(etype=dtype.real, given=True)
    f, g = Function(real=True)
    Eq << apply(Less(f(x), p) & Element(x, A) | Less(g(x), p) & NotElement(x, A), wrt=p)

    Eq << Eq[1].apply(Logic.Cond.given.Or.OrNot, cond=Element(x, A))

    Eq << Logic.And_And.given.And.Cond.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].apply(Logic.BFn.of.BFnIte.Cond, invert=True, swap=True, ret=1), Eq[-1].apply(Logic.BFn.of.BFnIte.Cond, swap=True, ret=1)

    Eq <<= Eq[-2] & Eq[0], Eq[-1] & Eq[0]

    Eq << Logic.OrAndS.of.And_Or.apply(Eq[-1])

    Eq << Logic.OrAndS.of.And_Or.apply(Eq[-2])


if __name__ == '__main__':
    run()

# created on 2019-08-05
