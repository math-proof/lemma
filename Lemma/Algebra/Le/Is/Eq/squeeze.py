from util import *


@apply
def apply(given):
    x, a = given.of(LessEqual)
    assert x >= a
    return Equal(x, a)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    x = Symbol(domain=Interval(1, oo))

    Eq << apply(LessEqual(x, 1))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-2].this.apply(Bool.Imp.Is.Or_Not)

    Eq << Eq[-1].apply(Bool.ImpNot.given.Or)


if __name__ == '__main__':
    run()

# created on 2019-11-26
