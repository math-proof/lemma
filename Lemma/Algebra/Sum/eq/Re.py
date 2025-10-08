from util import *


@apply
def apply(self, *, simplify=True):
    arg, *limits = self.of(Sum[Re])
    sum = Sum(arg, *limits)
    if simplify:
        sum = sum.simplify()
    return Equal(self, Re(sum))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n = Symbol(integer=True, nonnegative=True, given=False)
    z = Symbol(complex=True, shape=(oo,))
    k = Symbol(integer=True)
    Eq << apply(Sum[k:n](Re(z[k])))

    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.rhs.arg.apply(Algebra.Sum.eq.Add.pop)

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq << Bool.Cond.of.All_Imp.apply(Eq[-1], n, 0)





if __name__ == '__main__':
    run()
# created on 2023-06-03
# updated on 2023-06-27
