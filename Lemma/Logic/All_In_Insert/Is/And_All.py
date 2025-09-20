from util import *


def doit(All, self):
    xi, (i, s), *limits = self.of(All)

    sgm = All.identity(xi)
    for t in s.of(FiniteSet):
        sgm = All.operator(sgm, xi._subs(i, t))

    assert limits
    return All(sgm, *limits)

@apply
def apply(self):
    return doit(All, self)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    x = Symbol(real=True, shape=(oo, oo))
    i, j, a, b, c, d = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)

    Eq << apply(All[j:{a, b, c, d}, i:m](x[i, j] > 0))

    Eq << Iff(All[i:m](Equal(Bool(All[j:{a, b, c, d}](x[i, j] > 0)), 1)), All[j:{a, b, c, d}, i:m](x[i, j] > 0), plausible=True)

    Eq << Eq[-1].this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].this.find(Bool, All).apply(Logic.AllIn_Insert.Is.And_All)

    Eq << Eq[-1].this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].reversed

if __name__ == '__main__':
    run()

# created on 2018-12-04
