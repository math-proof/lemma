from util import *


@apply
def apply(self):
    (function, *limits), *variable_count = self.of(Difference[Sum])

    rhs = Sum(Difference(function, *variable_count).simplify(), *limits)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Bool

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    x = Symbol(real=True)
    d = Symbol(integer=True, positive=True, given=False)
    Eq << apply(Difference(Sum[i:n](f[i](x)), (x, d)))

    Eq.initial = Eq[0].subs(d, 1)

    Eq << Eq.initial.this.lhs.apply(Discrete.Diff.eq.Sum.One)

    Eq.induct = Eq[0].subs(d, d + 1)

    Eq << Discrete.EqDiff.of.Eq.apply(Eq[0], (x, 1))

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.apply(Discrete.Diff.eq.Sum.One)

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Bool.Eq.of.Eq.All_Imp.apply(Eq.initial, Eq[-1], n=d, start=1)


if __name__ == '__main__':
    run()

# created on 2020-10-11
del One
from . import One
from . import Binom
