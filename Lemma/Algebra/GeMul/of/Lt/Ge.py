from util import *


@apply
def apply(lt, ge):
    a, b = lt.of(Less)
    x, y = ge.of(GreaterEqual)
    z = b - a
    return GreaterEqual(z * x,  z * y)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, b, x, y = Symbol(real=True)
    Eq << apply(a < b, x >= y)

    Eq << Algebra.Gt_0.of.Lt.apply(Eq[0])

    Eq << Algebra.GeMul.of.Gt_0.Ge.apply(Eq[-1], Eq[1])




if __name__ == '__main__':
    run()
# created on 2019-12-14
