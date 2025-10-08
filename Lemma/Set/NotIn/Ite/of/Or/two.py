from util import *


@apply
def apply(given, wrt=None):
    or_eqs = given.of(Or)

    assert len(or_eqs) == 2
    from Lemma.Bool.BFnIte.of.OrAndS import expr_cond_pair
    return NotElement(Piecewise(*expr_cond_pair(NotElement, or_eqs, wrt)).simplify(), wrt)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,), given=True)
    A, S = Symbol(etype=dtype.real[k], given=True)
    f, g = Function(shape=(k,), real=True)
    Eq << apply(NotElement(f(x), S) & Element(x, A) | NotElement(g(x), S) & NotElement(x, A), wrt=S)

    Eq << Eq[1].apply(Bool.Cond.given.Or.OrNot, cond=Element(x, A))

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].apply(Bool.BFn.of.BFnIte.Cond, invert=True, swap=True, ret=1), Eq[-1].apply(Bool.BFn.of.BFnIte.Cond, ret=0)

    Eq <<= Eq[-2] & Eq[0], Eq[-1] & Eq[0]

    Eq << Bool.OrAndS.of.And_Or.apply(Eq[-1])

    Eq << Bool.OrAndS.of.And_Or.apply(Eq[-2])




if __name__ == '__main__':
    run()
# created on 2021-06-12
# updated on 2023-05-14
