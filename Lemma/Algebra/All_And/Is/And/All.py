from util import *


@apply
def apply(self, simplify=True):
    from Lemma.Finset.Sum_Add.eq.AddSumS import associate
    return associate(All, self, simplify=simplify)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    f, h = Function(real=True)
    Eq << apply(All[i:n]((f(i) > 0) & (h(i) > 0)))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Bool.All.All.of.All_And)

    Eq << Eq[-1].this.rhs.apply(Bool.All_And.given.All.All)


if __name__ == '__main__':
    run()

# created on 2018-12-22
