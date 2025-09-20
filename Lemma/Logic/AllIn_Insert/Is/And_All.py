from util import *


def doit(All, self):
    xi, (i, s) = self.of(All)

    sgm = self.identity(xi)
    assert s.is_FiniteSet
    for t in s.args:
        sgm = All.operator(sgm, xi._subs(i, t))

    return sgm


@apply
def apply(self):
    return doit(All, self)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    x = Symbol(real=True, shape=(oo,))
    i, a, b, c, d = Symbol(integer=True)


    Eq << apply(All[i:{a, b, c, d}](x[i] > 0))

    Eq << Iff(All[i:{a}](x[i] > 0), x[a] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Iff(All[i:{b}](x[i] > 0), x[b] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Logic.IffAndS.of.Iff.Iff.apply(Eq[-2], Eq[-1])

    Eq << Iff(All[i:{c}](x[i] > 0), x[c] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Logic.IffAndS.of.Iff.Iff.apply(Eq[-2], Eq[-1])

    Eq << Iff(All[i:{d}](x[i] > 0), x[d] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Logic.IffAndS.of.Iff.Iff.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-03-29
