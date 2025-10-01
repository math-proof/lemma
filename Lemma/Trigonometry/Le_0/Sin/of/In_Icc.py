from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    assert domain in Interval(-S.Pi, 0)
    return LessEqual(sin(x), 0)


@prove
def prove(Eq):
    from Lemma import Set, Trigonometry

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(-S.Pi, 0)))

    Eq << Set.Neg.In.Icc.of.In_Icc.apply(Eq[0])

    Eq << Trigonometry.Ge_0.Sin.of.In_Icc.apply(Eq[-1])
    Eq << -Eq[-1]


if __name__ == '__main__':
    run()
# created on 2020-11-20
