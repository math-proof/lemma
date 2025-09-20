from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.doit.outer.setlimit import doit
    return doit(All, self)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(real=True, shape=(oo, oo))
    i, j, a = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(All[j:f(i, j) > 0, i:{a}](x[i, j] > 0))

    Eq << Iff(All[i:{a}](Equal(Bool(All[j:f(i, j) > 0](x[i, j] > 0)), 1)), All[j:f(i, j) > 0, i:{a}](x[i, j] > 0), plausible=True)

    Eq << Eq[-1].this.lhs.expr.lhs.apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()

# created on 2018-12-05
# updated on 2023-08-26
