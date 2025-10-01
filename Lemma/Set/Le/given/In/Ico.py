from util import *


@apply(simplify=False)
def apply(given):
    n, b = given.of(LessEqual)
    assert n.is_integer
    return Element(n, Range(-oo, b + 1))


@prove
def prove(Eq):
    from Lemma import Algebra
    n, b = Symbol(integer=True, given=True)

    Eq << apply(n <= b)

    Eq << Eq[-1].simplify()

    Eq << Algebra.Le.given.Lt.One.apply(Eq[0])


if __name__ == '__main__':
    run()

# created on 2021-05-18
