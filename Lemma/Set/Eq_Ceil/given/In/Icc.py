from util import *


@apply
def apply(eq):
    x, a = eq.of(Equal[Ceil])
    return Element(x, Interval(a - 1, a, left_open=True, right_open=False))


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(real=True)
    a = Symbol(integer=True)
    Eq << apply(Equal(Ceil(x), a + 1))

    Eq << Set.EqCeil.of.In_Ioc.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2023-05-29
