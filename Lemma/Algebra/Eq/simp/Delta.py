from util import *



@apply
def apply(given):
    x, y = given.of(Equal[KroneckerDelta, 1])
    return Equal(x, y)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    n = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(n,))

    Eq << apply(Equal(KroneckerDelta(x, y), 1))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.lhs.apply(Algebra.Delta.eq.Ite)

    Eq << Eq[-1].this.rhs.lhs.apply(Algebra.Delta.eq.Ite)


if __name__ == '__main__':
    run()
# created on 2019-04-20
