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

    Eq << Eq[1].this.find(And).apply(Logic.OrAndS.of.And_Or, simplify=None)





if __name__ == '__main__':
    run()
# created on 2018-02-22
# updated on 2023-05-13

