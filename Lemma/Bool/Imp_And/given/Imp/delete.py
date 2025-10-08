from util import *


@apply
def apply(given, index=-1):
    [*eqs], rhs = given.of(Imply[And, Boolean])
    del eqs[index]
    et = And(*eqs)
    return Imply(et, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    x = Symbol(integer=True)
    A = Symbol(etype=dtype.integer)
    Eq << apply(Imply(Equal(f[n], g[n]) & Element(x, A), Equal(f[n + 1], g[n + 1])))

    Eq << Bool.ImpAndS.of.Imp.apply(Eq[1], cond=Element(x, A))
    Eq << Bool.Imp.of.Imp_And.apply(Eq[-1], index=0)


if __name__ == '__main__':
    run()
# created on 2019-04-30
