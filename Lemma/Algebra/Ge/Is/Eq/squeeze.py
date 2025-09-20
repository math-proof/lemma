from util import *


@apply
def apply(self):
    x, b = self.of(GreaterEqual)
    assert x <= b
    return Equal(x, b)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    a = Symbol(integer=True)
    b = Symbol(integer=True, given=True)
    x = Symbol(domain=Range(a, b + 1), given=True)
    Eq << apply(x >= b)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Eq.of.Ge.squeeze)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ge.of.Eq)





if __name__ == '__main__':
    run()
# created on 2019-06-04
# updated on 2023-11-11

