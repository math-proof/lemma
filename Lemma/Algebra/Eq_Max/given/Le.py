from util import *


@apply
def apply(given):
    [*args], x = given.of(Equal[Max])
    assert x in args
    args.remove(x)
    return Max(*args) <= x


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(integer=True)
    Eq << apply(Equal(x, Max(x, y)))

    Eq << Algebra.Eq_Max.given.Ge.apply(Eq[0])
    Eq << Eq[-1].reversed



if __name__ == '__main__':
    run()
# created on 2023-04-23
