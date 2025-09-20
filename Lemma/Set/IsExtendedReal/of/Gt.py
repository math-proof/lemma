from util import *


@apply
def apply(given):
    n, b = given.of(Greater)
    return Element(n, Interval(-oo, oo, right_open=False))


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(extended_complex=True)
    b = Symbol(real=True)
    Eq << apply(x > b)

    Eq << Eq[-1].simplify()
    Eq << Algebra.Gt.given.And.strengthen.apply(Eq[-1], upper=b)


if __name__ == '__main__':
    run()
# created on 2020-03-31
