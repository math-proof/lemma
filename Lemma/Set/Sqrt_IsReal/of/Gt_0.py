from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return Element(sqrt(x), Reals)


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    x = Symbol(real=True, given=True)
    Eq << apply(x > 0)

    Eq << Algebra.Ge_0.of.Gt_0.apply(Eq[0])

    Eq << Set.Sqrt_IsReal.of.Ge_0.apply(Eq[-1], simplify=None)


if __name__ == '__main__':
    run()
# created on 2021-04-20
