from util import *


@apply
def apply(given, wrt=None):
    or_eqs = given.of(Or)
    from Lemma.Bool.BFnIte.of.OrAndS import expr_cond_pair
    assert len(or_eqs) == 2
    return NotElement(wrt, Piecewise(*expr_cond_pair(NotElement, or_eqs, wrt, reverse=True)).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,), given=True)
    A = Symbol(etype=dtype.real[k], given=True)
    f, g = Function(etype=dtype.real[k])
    Eq << apply(NotElement(y, f(x)) & Element(x, A) | NotElement(y, g(x)) & NotElement(x, A), wrt=y)

    Eq << Eq[1].apply(Bool.Cond.given.Or.OrNot, cond=Element(x, A))

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].this.apply(Bool.BFn.of.BFnIte.Cond, invert=True, swap=True, ret=1), Eq[-1].this.apply(Bool.BFn.of.BFnIte.Cond, ret=0)

    Eq <<= Eq[-2] & Eq[0], Eq[-1] & Eq[0]

    Eq << Bool.OrAndS.of.And_Or.apply(Eq[-1])

    Eq << Bool.OrAndS.of.And_Or.apply(Eq[-2])




if __name__ == '__main__':
    run()
# created on 2021-06-09
# updated on 2023-05-14
