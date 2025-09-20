from util import *


@apply
def apply(self):
    p, q = self.of(Iff)
    return Iff(q.invert(), p.invert())


@prove
def prove(Eq):
    from Lemma import Logic

    p, q = Symbol(bool=True)
    Eq << apply(Iff(p, q))

    Eq << Eq[0].this.lhs.apply(Logic.Iff.Is.Or.And)

    Eq << Eq[-1].this.rhs.apply(Logic.Iff.Is.Or.And)


if __name__ == '__main__':
    run()
# created on 2022-01-27
