from util import *


@apply
def apply(is_nonzero, n, x2):
    x1 = is_nonzero.of(Unequal[0])
    assert n >= 1
    i, j = Symbol(integer=True)
    return Equal(Det([Stack[j:n + 1](x2 ** j), Stack[j:n + 1, i:n](j ** i * x1 ** j)]), x1 ** Binomial(n, 2) * (x1 - x2) ** n * Product[i:n](factorial(i)))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor

    n = Symbol(integer=True, positive=True)
    x1, x2 = Symbol(complex=True)
    Eq << apply(Unequal(x2, 0), n, x1)

    Eq << Algebra.Inv.ne.Zero.of.Ne_0.apply(Eq[0])

    r = Symbol(Eq[-1].lhs * x1)
    Eq << r.this.definition * x2

    Eq << Eq[-1].reversed

    Eq.eq = Eq[1].subs(Eq[-1])

    Eq << Eq.eq.rhs.this.find(Add).apply(Algebra.AddMulS.eq.Mul_Add)

    Eq << Eq[-1].this.find(Pow[Mul]).apply(Algebra.Pow.eq.Mul.split.base)

    Eq << Eq[-1].this.rhs.find(Binomial).apply(Discrete.Binom.eq.Div.Binom)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).expand()

    Eq << Eq.eq.subs(Eq[-1])

    j, i = Eq[-1].find(Stack[Tuple[2]]).variables
    Eq << (Eq[-1].lhs.arg @ Stack[j:n + 1, i:n + 1](Eq[2].lhs ** j * KroneckerDelta(i, j))).this.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.find(Mul ** Symbol).apply(Algebra.Pow.eq.Mul.split.base)

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack.Ite.eq.Block)

    Eq << Discrete.EqDet.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Discrete.DetBlock_Stack_Pow.eq.Mul_Prod_Factorial.vandermonde)

    Eq << Eq[-1].subs(r.this.definition)

    Eq << Eq[-1].this.lhs.apply(Discrete.Det.eq.Mul)

    Eq << Eq[-1] * x2 ** binomial(n, 2)

    Eq << Eq[-1].this.lhs.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial.doit)

    Eq << Eq[-1].this.find(Symbol ** Add).expand()

    Eq << Eq[-1] * x2 ** n

    Eq << Eq[-1].this.rhs.find((~Add) ** Symbol).apply(Algebra.Add.eq.Mul.together)

    Eq << Eq[-1].this.rhs.find(Mul ** Symbol).apply(Algebra.Pow.eq.Mul.split.base)





if __name__ == '__main__':
    run()
# created on 2020-10-14
# updated on 2021-11-23
