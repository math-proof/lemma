from util import *


@apply
def apply(given):
    x = given.of(Equal[Ceil, 0])
    return Element(x, Interval(-1, 0, left_open=True))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Int

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(Ceil(x), 0))

    Eq << Set.In_Ico.given.Le.Lt.apply(Eq[-1])

    Eq << Algebra.Le_Ceil.apply(x)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Int.LtSubCeil_1.apply(x)
    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-08-12
