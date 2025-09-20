from util import *


@apply
def apply(given, X):
    A, B = given.of(Subset)
    return Imply(Subset(X, A), Subset(X, B))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    n = Symbol(integer=True, positive=True)
    A, B = Symbol(etype=dtype.integer[n])
    X = Symbol(etype=dtype.integer[n], given=True)
    Eq << apply(Subset(A, B), X)

    Eq << Eq[1].this.apply(Logic.Imp.given.Imp.And)

    Eq << Set.EqInter.of.Subset.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2022-09-20
