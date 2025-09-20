from util import *


@apply
def apply(self, *, cond=None, wrt=None, evaluate=False):
    from Lemma.Algebra.Sum.eq.Add.split import split
    return split(All, self, cond, wrt=wrt)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(integer=True)
    f = Function(real=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(All[x:A](f(x) > 0), cond=B)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.rhs.apply(Algebra.All.All.given.All.limits_union)

    Eq << Eq[-1].this.lhs.apply(Logic.AllOr.of.All.All)


if __name__ == '__main__':
    run()

# created on 2018-04-23
