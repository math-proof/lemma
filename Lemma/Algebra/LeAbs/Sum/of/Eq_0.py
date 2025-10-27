from util import *


@apply
def apply(is_zero, self, pivot=-1, i=None):
    fn1 = is_zero.of(Equal[0])
    args, (k, S[0], n) = self.of(Sum[Mul])
    n -= 1
    assert n >= 0
    fk, gk = std.array_split(args, pivot)
    fk = Mul(*fk)
    gk = Mul(*gk)
    if i is None:
        i = self.generate_var(integer=True, excludes={k, n})
    assert fn1 == fk._subs(k, n + 1)
    return Abs(self) <= Maxima[k:n + 1](Abs(fk._subs(k, k + 1) - fk)) * Sum[k:n + 1](Abs(Sum[i:k + 1](gk._subs(k, i))))


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    n = Symbol(integer=True, nonnegative=True)
    i, k = Symbol(integer=True)
    f, g = Function(real=True)
    Eq << apply(Equal(f(n + 1), 0), Sum[k:n + 1](f(k) * g(k)), i=i)

    Eq << Algebra.Sum.eq.Neg.Sum.of.Eq_0.apply(Eq[0], Eq[1].find(Sum), i=i)

    Eq << Algebra.EqAbs.of.Eq.apply(Eq[-1])

    Eq << Algebra.AbsSum.le.Sum_Abs.apply(Eq[-1].rhs.arg)

    Eq << Algebra.Le.of.Eq.Le.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.find(Abs[Mul]).apply(Algebra.Abs.eq.Mul)

    Eq << Algebra.All_Le_Maxima.apply(Eq[1].find(Maxima))

    Eq << Eq[-1].this.expr.apply(Algebra.LeMul.of.Le, Eq[-2].rhs.find(Abs[Sum]))

    Eq << Algebra.LeSum.of.All_Le.apply(Eq[-1])

    Eq << Nat.Le.of.Le.Le.apply(Eq[-4], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-06-03
