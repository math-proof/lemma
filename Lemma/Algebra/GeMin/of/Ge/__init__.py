from util import *


@apply
def apply(given, m):
    lhs, rhs = given.of(GreaterEqual)
    return GreaterEqual(Min(lhs, m), Min(rhs, m))


@prove
def prove(Eq):
    from Lemma import Algebra
    x, y, z = Symbol(real=True, given=True)

    Eq << apply(x >= y, z)

    Eq << Eq[-1] - y

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Min)

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Min)

    Eq << Eq[0] - y

    Eq << Algebra.Eq_0.Min.of.Ge_0.apply(Eq[-1])

    Eq << Algebra.EqMin.of.Eq.apply(Eq[-1], -y + z)

    Eq << GreaterEqual(Min(x - y, -y + z), Min(x - y, 0, -y + z), plausible=True)

    Eq << Eq[-1].subs(Eq[-2])


if __name__ == '__main__':
    run()
# created on 2019-05-28

del Ge
from . import Ge
