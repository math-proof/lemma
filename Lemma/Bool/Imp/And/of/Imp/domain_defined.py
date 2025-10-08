from util import *


@apply(simplify=False)
def apply(given, t):
    lhs, rhs = given.of(Imply)
    domain = given.domain_defined(t)
    cond = Element(t, domain)
    return Imply(cond & lhs, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    f, g = Symbol(bool=True, shape=(n,))
    Eq << apply(Imply(f[k], g[k]), k)

    Eq << Bool.ImpAndS.of.Imp.apply(Eq[0], cond=Eq[1].find(Element))

    Eq << Eq[-1].this().rhs.find(Element).simplify()


if __name__ == '__main__':
    run()
# created on 2023-04-13
