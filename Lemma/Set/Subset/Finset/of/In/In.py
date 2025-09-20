from util import *


@apply
def apply(contains1, contains2):
    x, A = contains1.of(Element)
    y, S[A] = contains2.of(Element)

    return Subset({x, y}, A)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic
    x, y = Symbol(integer=True)
    S = Symbol(etype=dtype.integer)

    Eq << apply(Element(x, S), Element(y, S))

    Eq << Set.Subset.given.All_In.apply(Eq[-1])

    Eq << Eq[-1].this.apply(Logic.AllIn_Insert.Is.And_All)

    Eq << Logic.And_And.given.And.Cond.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-03-29
