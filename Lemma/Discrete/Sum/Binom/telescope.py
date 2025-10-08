from util import *


@apply
def apply(self):
    ((n, k), S[n + k], (fk1, fk)), (k, S[0], S[n + 1]) = self.of(Sum[Binomial * (-1) ** Expr * (Expr - Expr)])
    S[fk1] = fk._subs(k, k + 1)
    n += 1
    return Equal(self, Sum[k:n + 1]((-1) ** (n - k) * binomial(n, k) * fk))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Bool

    f = Function(real=True)
    x = Symbol(real=True)
    n = Symbol(integer=True, nonnegative=True)
    k = Symbol(integer=True)
    Eq << apply(Sum[k:n + 1]((-1) ** (n - k) * Binomial(n, k) * (f(x + k + 1) - f(x + k))))

    Eq.diff = Discrete.Diff.eq.Sum.Binom.apply(Difference(f(x), (x, n)), k)

    Eq.diff_1 = Eq.diff.subs(x, x + 1)

    Eq <<= Eq.diff.subs(n, n + 1)

    Eq << Eq[-1].this.lhs.apply(Discrete.Diff.split, n)

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq.diff_1 - Eq.diff

    Eq << Eq[-1].this.rhs.apply(Algebra.AddSumS.eq.Sum_Add_Sum)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.AddMulS.eq.Mul_Add)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-1], Eq[-4])




if __name__ == '__main__':
    run()
# created on 2023-06-03
