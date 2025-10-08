from util import *


@apply
def apply(given, wrt=None):
    or_eqs = given.of(Or)
    assert len(or_eqs) == 2
    from Lemma.Bool.BFnIte.of.OrAndS import expr_cond_pair
    return Unequal(wrt, Piecewise(*expr_cond_pair(Unequal, or_eqs, wrt, reverse=True)).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    k = Symbol(integer=True, positive=True)
    x, p = Symbol(real=True, shape=(k,), given=True)
    A = Symbol(etype=dtype.real[k], given=True)
    f, g = Function(shape=(k,), real=True)
    Eq << apply(Unequal(p, f(x)) & Element(x, A) | Unequal(g(x), p) & NotElement(x, A), wrt=p)

    Eq << Eq[1].apply(Bool.Cond.given.Or.OrNot, cond=Element(x, A))

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].apply(Bool.BFn.of.BFnIte.Cond, invert=True, swap=True, ret=1), Eq[-1].apply(Bool.BFn.of.BFnIte.Cond, swap=True, ret=1)

    Eq <<= Eq[-2] & Eq[0], Eq[-1] & Eq[0]

    Eq << Bool.OrAndS.of.And_Or.apply(Eq[-1])

    Eq << Bool.OrAndS.of.And_Or.apply(Eq[-2])


if __name__ == '__main__':
    run()

# created on 2020-02-07
