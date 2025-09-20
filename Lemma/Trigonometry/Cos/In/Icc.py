from util import *


@apply(simplify=False)
def apply(x):
    return Element(cos(x), Interval(-1, 1))


@prove
def prove(Eq):
    from Lemma import Trigonometry, Algebra, Set

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << Trigonometry.Add_.SquareCos.SquareSin.eq.One.apply(x)

    Eq << Algebra.Le.of.Eq_Add.bounded.apply(Eq[1], 1)

    Eq << Eq[-1].this.apply(Set.LeSquare.Is.In.Icc)




if __name__ == '__main__':
    run()
# created on 2023-10-03
