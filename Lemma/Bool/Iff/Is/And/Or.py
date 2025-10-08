from util import *


@apply
def apply(self):
    p, q = self.of(Iff)
    return (p.invert() | q) & (q.invert() | p)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    p, q = Symbol(bool=True)
    Eq << apply(Iff(p, q))

    Eq << Eq[0].this.lhs.apply(Bool.Iff.Is.And.Imp)

    Eq << Eq[-1].this.find(Imply).apply(Bool.Imp.Is.Or_Not)

    Eq << Eq[-1].this.find(Imply).apply(Bool.Imp.Is.Or_Not)


if __name__ == '__main__':
    run()
# created on 2022-01-27
