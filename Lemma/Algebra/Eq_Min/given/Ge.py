from util import *


@apply
def apply(given):
    [*args], x = given.of(Equal[Min])
    assert x in args
    args.remove(x)
    return Max(*args) >= x


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(integer=True)
    Eq << apply(Equal(x, Min(x, y)))

    Eq << Algebra.Eq_Min.given.Le.apply(Eq[0])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2023-04-23
