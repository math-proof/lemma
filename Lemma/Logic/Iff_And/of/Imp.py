from util import *


@apply
def apply(given):
    fx, fy = given.of(boolalg.Imply)
    return Iff(fx, fx & fy)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(boolalg.Imply(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq.suffice, Eq.necessary = Logic.Iff.given.Imp.Imp.apply(Eq[1])

    Eq << Logic.Imp_And.of.ImpAnd.apply(Eq[0])



if __name__ == '__main__':
    run()

# created on 2018-02-03
