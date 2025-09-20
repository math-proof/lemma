from util import *


@apply
def apply(given, *, cond=None, wrt=None):
    from Lemma.Logic.All.All.of.All import split
    given = split(All, given, cond, wrt)
    return given


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(real=True)
    f = Function(integer=True, shape=())
    d = Symbol(real=True, positive=True)
    Eq << apply(All[x:Interval(-d, d, left_open=True, right_open=True)](f(x) > 0), cond=x < 0)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Logic.All.All.of.All, cond=x < 0)

    Eq << Eq[-1].this.rhs.apply(Algebra.All.given.And.All.split, cond=x < 0)


if __name__ == '__main__':
    run()
# created on 2023-10-22
