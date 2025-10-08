from util import *


@apply
def apply(self):
    from Lemma.Bool.All_In_Insert.Is.And_All import doit
    return doit(Any, self)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    x = Symbol(real=True, shape=(oo, oo))
    i, j, a, b, c, d = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)

    Eq << apply(Any[j:{a, b, c, d}, i:m](x[i, j] > 0))

    Eq << Iff(Any[i:m](Equal(functions.Bool(Any[j:{a, b, c, d}](x[i, j] > 0)), 1)), Any[j:{a, b, c, d}, i:m](x[i, j] > 0), plausible=True)

    Eq << Eq[-1].this.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    Eq << Eq[-1].this.find(functions.Bool, Any).apply(Algebra.Any.Is.Or.doit.setlimit)

    Eq << Eq[-1].this.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2019-02-10
