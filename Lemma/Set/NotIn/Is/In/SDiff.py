from util import *


@apply
def apply(self):
    x, s = self.of(NotElement)

    return Element(x, x.domain - s)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    Eq << apply(NotElement(x, S))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Set.In.SDiff.of.NotIn)

    Eq << Eq[-1].this.rhs.apply(Set.NotIn.given.In.SDiff)




if __name__ == '__main__':
    run()
# created on 2023-05-21
