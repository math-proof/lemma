from util import *


@apply
def apply(given):
    x = given.of(Equal[Abs, 0])
    assert x.is_extended_real
    return Equal(x, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Int

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(abs(x), 0))

    Eq << Eq[0].this.lhs.apply(Int.Abs.eq.IteGe_0)

    Eq << Bool.OrAndS.of.BFn_Ite.apply(Eq[-1])
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-03-15
