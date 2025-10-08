from util import *


@apply
def apply(given, var=None):
    lhs, rhs = given.of(Imply)
    assert lhs._has(var) and rhs._has(var)
    return Imply(Exists[var](lhs), Exists[var](rhs))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    p, q, r = Function(real=True)
    x = Symbol(real=True)
    Eq << apply(Imply(p(x) >= 0, q(x) >= 0), var=x)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Bool.Imp.Any.of.Imp, x)

    Eq << Eq[-1].this.rhs.apply(Bool.Imp.given.Imp.Any, x)


if __name__ == '__main__':
    run()
# created on 2023-11-10

from . import of
