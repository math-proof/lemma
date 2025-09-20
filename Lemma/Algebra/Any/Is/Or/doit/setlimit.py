from util import *


@apply
def apply(self):
    from Lemma.Logic.AllIn_Insert.Is.And_All import doit
    return doit(Any, self)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    x = Symbol(real=True, shape=(oo,))
    i, a, b, c, d = Symbol(integer=True)

    Eq << apply(Any[i:{a, b, c, d}](x[i] > 0))

    Eq << Iff(Any[i:{a}](x[i] > 0), x[a] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Iff(Any[i:{b}](x[i] > 0), x[b] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Logic.Iff.Or.of.Iff.Iff.apply(Eq[-2], Eq[-1])

    Eq << Iff(Any[i:{c}](x[i] > 0), x[c] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Logic.Iff.Or.of.Iff.Iff.apply(Eq[-2], Eq[-1])

    Eq << Iff(Any[i:{d}](x[i] > 0), x[d] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Logic.Iff.Or.of.Iff.Iff.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-02-09
