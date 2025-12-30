from util import *


@apply(simplify=None)
def apply(given):
    n, b = given.of(LessEqual)
    assert n > 0
    return Element(1 / n, Interval(1 / b, oo))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    n = Symbol(real=True, positive=True)
    b = Symbol(real=True)
    Eq << apply(n <= b)

    Eq << Set.In_Ico.given.Le.Lt.apply(Eq[1])

    Eq << Greater(n, 0, plausible=True)

    Eq << Algebra.Gt.of.Gt.Le.apply(Eq[0], Eq[-1])

    Eq << Algebra.LeDiv.of.Gt_0.Le.apply(Eq[-2], Eq[0])


    Eq << Algebra.GeDiv.of.Gt_0.Ge.apply(Eq[-2], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-10-04
