from util import *


@apply
def apply(given, *, cond=None):
    from Lemma.Logic.OrAndOr.of.OrAnd__OrAnd import collect
    return collect(given, cond)

@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, y = Symbol(real=True, given=True)
    f, h, g = Function(real=True)
    Eq << apply(Unequal(x, y) | Equal(f(x), g(y)) & (y > 0) | Equal(h(x), g(y)) & (y > 0), cond=y > 0)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Logic.OrAndOr.of.OrAnd__OrAnd, cond=y > 0)
    Eq << Eq[-1].this.rhs.apply(Logic.Or_OrAndS.given.Or_And_Or, cond=y > 0)


if __name__ == '__main__':
    run()
# created on 2020-02-16
