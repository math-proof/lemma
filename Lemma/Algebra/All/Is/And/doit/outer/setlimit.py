from util import *


def doit(All, self):
    xi, * limits, (i, s) = self.of(All)

    assert limits
    assert s.is_FiniteSet
    sgm = self.identity(xi)
    for t in s.args:
        _limits = []
        for (j, *ab) in limits:
            _limits.append((j, *(c._subs(i, t) for c in ab)))

        sgm = All.operator(sgm, All(xi._subs(i, t), *_limits))

    return sgm


@apply
def apply(self):
    return doit(All, self)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    x = Symbol(real=True, shape=(oo, oo))
    i, j, a, b, c, d = Symbol(integer=True)
    f = Function(integer=True)


    Eq << apply(All[j:f(i), i:{a, b, c, d}](x[i, j] > 0))

    Eq << Iff(All[j:f(i), i:{a}](x[i, j] > 0), All[j:f(a)](x[a, j] > 0), plausible=True)

    Eq << Eq[-1].this.lhs.apply(Algebra.All.doit.outer.setlimit)

    Eq << Iff(All[j:f(i), i:{b}](x[i, j] > 0), All[j:f(b)](x[b, j] > 0), plausible=True)

    Eq << Eq[-1].this.lhs.apply(Algebra.All.doit.outer.setlimit)

    Eq << Bool.IffAndS.of.Iff.Iff.apply(Eq[-2], Eq[-1])

    Eq << Iff(All[j:f(i), i:{c}](x[i, j] > 0), All[j:f(c)](x[c, j] > 0), plausible=True)

    Eq << Eq[-1].this.lhs.apply(Algebra.All.doit.outer.setlimit)

    Eq << Bool.IffAndS.of.Iff.Iff.apply(Eq[-2], Eq[-1])

    Eq << Iff(All[j:f(i), i:{d}](x[i, j] > 0), All[j:f(d)](x[d, j] > 0), plausible=True)

    Eq << Eq[-1].this.lhs.apply(Algebra.All.doit.outer.setlimit)

    Eq << Bool.IffAndS.of.Iff.Iff.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-12-21
