from util import *


@apply
def apply(given, wrt=None, reverse=True):
    from Lemma.Logic.BFnIte.of.OrAndS import expr_cond_pair
    or_eqs = given.of(Or)

    return Equal(Piecewise(*expr_cond_pair(Equal, or_eqs, wrt, reverse=reverse)).simplify(), wrt)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    k = Symbol(integer=True, positive=True)
    x, p = Symbol(real=True, shape=(k,), given=True)
    A, B = Symbol(etype=dtype.real[k], given=True)
    f, g, h = Function(shape=(k,), real=True)
    Eq << apply(Equal(f(x), p) & Element(x, A) | Equal(p, g(x)) & Element(x, B - A) | Equal(p, h(x)) & NotElement(x, A | B), wrt=p)

    Eq << Logic.OrAndS.of.BFn_Ite.apply(Eq[1])

    Eq << Eq[-1].this.args[1].args[0].reversed

    Eq << Eq[-1].this.args[-1].args[0].reversed




if __name__ == '__main__':
    run()
# created on 2023-04-30
# updated on 2023-05-20
