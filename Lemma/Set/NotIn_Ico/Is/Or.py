from util import *


@apply
def apply(given):
    e, S = given.of(NotElement)
    start, stop = S.of(Range)

    lower_bound = e < start
    upper_bound = e >= stop
    return Or(lower_bound, upper_bound)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    e, a, b = Symbol(integer=True, given=True)
    Eq << apply(NotElement(e, Range(a, b)))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Set.Or.of.NotIn_Ico)

    Eq << Eq[-1].this.lhs.apply(Set.NotIn.Ico.of.Or)



if __name__ == '__main__':
    run()
# created on 2021-12-17
