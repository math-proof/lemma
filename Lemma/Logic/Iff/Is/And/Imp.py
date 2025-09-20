from util import *


@apply
def apply(self):
    p, q = self.of(Iff)
    return And(Imply(p, q), Imply(q, p))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    p, q = Symbol(bool=True)
    Eq << apply(Iff(p, q))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.rhs.apply(Logic.Imp.Imp.given.Iff)

    Eq << Eq[-1].this.lhs.apply(Logic.Iff.of.Imp.Imp)


if __name__ == '__main__':
    run()
# created on 2022-01-27
