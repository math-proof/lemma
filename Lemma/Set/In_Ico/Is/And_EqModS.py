from util import *


@apply
def apply(given):
    x, domain = given.of(Element)
    a, b, d = domain.of(Range)
    assert x.is_integer
    assert d > 0
    return And(x >= a, x < b, Equal(x % d, a % d))

@prove
def prove(Eq):
    from Lemma import Set

    x, a, b = Symbol(integer=True)
    d = Symbol(integer=True, positive=True)
    Eq << apply(Element(x, Range(a, b, d)))

    Eq << Eq[0].this.lhs.apply(Set.In_Ico.Is.And.split.Ico)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Ico.Is.And)



if __name__ == '__main__':
    run()
# created on 2022-01-01
# updated on 2023-05-30
