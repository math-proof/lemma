from util import *


@apply
def apply(given, k=None):
    n = given.of(Equal[Expr % 2, 0])
    if k is None:
        k = Symbol(integer=True)

    return Any[k](Equal(n, k * 2))


@prove
def prove(Eq):
    from Lemma import Algebra

    # n = q * d + r
    n = Symbol(integer=True, given=True)
    r = Symbol(integer=True)
    Eq << apply(Equal(n % 2, 0))


    Eq << Eq[1].this.expr.apply(Algebra.EqMod.of.Eq, 2)




if __name__ == '__main__':
    run()
# created on 2023-05-26
