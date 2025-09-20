from util import *


@apply
def apply(given):
    abs_x, a = given.of(Less)
    x = abs_x.of(Expr ** 2)
    assert x.is_real
    return Less(x, sqrt(a)), Less(-sqrt(a), x)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a = Symbol(real=True)
    Eq << apply(x ** 2 < a ** 2)

    Eq << Algebra.LtAbs.of.Lt.Gt.apply(Eq[-2], Eq[-1].reversed)

    Eq << Algebra.LtSquare.of.Lt.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2020-01-15
# updated on 2023-06-18
