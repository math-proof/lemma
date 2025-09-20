from util import *


@apply(simplify=False)
def apply(given, *, cond=None):
    assert cond.is_bool
    return Imply(cond, given & cond), Imply(cond.invert(), given & cond.invert())


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    e = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq << Logic.And.Imp.of.Cond.split.apply(Eq[0], cond=e > 0)

    Eq << Logic.Imp_And.of.ImpAnd.apply(Eq[-2])
    Eq << Logic.Imp_And.of.ImpAnd.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-03-18
