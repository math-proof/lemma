from util import *


@apply
def apply(given, var=None):
    lhs, rhs = given.of(Imply)
    assert lhs._has(var) and rhs._has(var)
    return Imply(Exists[var](lhs), Exists[var](rhs))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    p, q, r = Function(real=True)
    x = Symbol(real=True)
    Eq << apply(Imply(p(x) >= 0, q(x) >= 0), var=x)

    Eq << Eq[0].this.apply(Logic.Imp.Is.ImpNotS)

    Eq << Eq[1].this.apply(Logic.Imp.Is.ImpNotS)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()
# created on 2023-11-10
