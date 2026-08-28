from util import *


from sympy.functions.combinatorial.numbers import Stirling
@apply
def apply(self):
    n, k = self.of(Stirling)
    i = n.generate_var(k.free_symbols, integer=True)
    return Equal(self, Sum[i:k + 1]((-1) ** (k - i) * binomial(k, i) * i ** n) / factorial(k))


@prove
def prove(Eq):
    from Lemma import Finset, Bool, Nat, Fin, Rat, Real

    k = Symbol(integer=True, nonnegative=True, given=False)
    n = Symbol(integer=True, nonnegative=True)
    Eq.hypothesis = apply(Stirling(n, k))

    Eq.induct = Eq.hypothesis.subs(k, k + 1)

    i = Eq.hypothesis.rhs.args[1].variable
    Eq << Finset.Stirling.eq.Add.recurrence.apply(Stirling(n + 1, k + 1))

    Eq << Eq[-1].subs(Eq.hypothesis)

    y = Symbol(Stack[n](Stirling(n, k + 1)))
    Eq << y[n].this.definition

    Eq << Eq[-1].subs(n, n + 1)

    Eq << Eq[-3].subs(Eq[-1].reversed, Eq[-2].reversed)

    j = Symbol(integer=True)
    # Eq << Eq[-1].this.apply(Algebra.eq.rsolve.linear, j)
    Eq << Finset.Eq.of.Eq.rsolve.apply(Eq[-1], j)

    Eq << Eq[-1].this.rhs.args[0].args[0].defun()

    Eq << Eq[-1].this.rhs.find(Mul[Sum]).apply(Finset.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-1].this.find(Sum).apply(Fin.Sum_BFn.comm)

    Eq << Eq[-1].this.find(Sum).apply(Finset.Sum.limits.separate)

    Eq << Eq[-1].this.find(Sum[Pow * Pow]).apply(Rat.Sum.eq.Mul.series.geometric)

    Eq << Eq[-1].this.find(Sum).find(Expr ** -1).base.apply(Rat.SubDivS1.eq.DivSub.of.Ne_0.Ne_0)

    Eq << Eq[-1].this.find(Binomial).apply(Finset.Binom.eq.Div.Binom.increase)

    Eq << Eq[-1].this.find(Sum).expr.apply(Nat.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Sum).apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Nat.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Sum).apply(Finset.Sum_Mul.eq.Mul_Sum)

    Eq << Eq[-1].this.find(Sum).apply(Finset.Sum.eq.Sub.push)

    Eq << Eq[-1].this.find(Sum).apply(Finset.Sum.Binom.eq.Delta.Zero)

    Eq << Eq[-1].this.find((~Pow) / Factorial).apply(Real.Pow_Add.eq.MulPowS.of.Gt_0, simplify=None)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(Finset.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-1].this.find(Mul ** Symbol).apply(Real.PowMul.eq.MulPowS)

    Eq.factor2mul = Finset.Factorial.eq.Mul.apply(factorial(k + 1))

    Eq << Eq[-1].subs(Eq.factor2mul.reversed)

    Eq << Eq[-1].this.rhs.apply(Nat.AddMulS.eq.Mul_Add)

    Eq << Eq[-1].this.find(Sum).apply(Finset.Sum.eq.Sub.push)

    Eq << Eq[-1].this.lhs.defun()

    Eq << Eq.induct * factorial(k + 1)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum.eq.Add.pop)

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Bool.Imp.of.All_Imp.apply(Eq[-1], n=k)





if __name__ == '__main__':
    run()
# created on 2020-10-13
# updated on 2023-08-26
