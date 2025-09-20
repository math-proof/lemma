from util import *


@apply
def apply(is_nonzero, x1, m, d):
    x2 = is_nonzero.of(Unequal[0])
    i, j = Symbol(integer=True)
    assert m > d
    return Equal(Det(BlockMatrix([Stack[j:m, i:d](j ** i * x1 ** j), Stack[j:m, i:m - d](j ** i * x2 ** j)])),
                 x2 ** Binomial(m - d, 2) * x1 ** Binomial(d, 2) * (x2 - x1) ** (d * (m - d)) * Product[i:d](factorial(i)) * Product[i:m - d](factorial(i)))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor

    d = Symbol(integer=True, positive=True)
    m = Symbol(domain=Range(d + 1, oo))
    x1, x2 = Symbol(complex=True)
    Eq << apply(Unequal(x2, 0), x1, m, d)

    Eq << Algebra.Inv.ne.Zero.of.Ne_0.apply(Eq[0])

    r = Symbol(Eq[-1].lhs * x1)
    Eq << r.this.definition * x2

    Eq << Eq[-1].reversed

    Eq << Eq[1].subs(Eq[-1])

    j, i = Eq[-1].find(Stack[Tuple[2]]).variables
    Eq << (Eq[-1].lhs.arg @ Stack[j:m, i:m](Eq[2].lhs ** j * KroneckerDelta(i, j))).this.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.find(Mul ** Symbol).apply(Algebra.Pow.eq.Mul.split.base)

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack.Ite.eq.Block)

    Eq << Discrete.EqDet.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Discrete.DetBlock_Stack_Pow.eq.Mul_Prod.vandermonde.ratio)

    Eq << Eq[-1].subs(r.this.definition)

    Eq << Eq[-1].this.lhs.apply(Discrete.Det.eq.Mul)

    Eq << Eq[-1] * x2 ** binomial(m, 2)

    Eq << Eq[-1].this.lhs.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial.doit)

    Eq << Eq[-1].this.find(Symbol ** ~Add).expand()

    Eq << Eq[-1].this.rhs.find((~Add) ** Mul).apply(Algebra.Add.eq.Mul.together)

    Eq << Eq[-1].this.rhs.find(Mul ** Mul).apply(Algebra.Pow.eq.Mul.split.base)

    Eq << Eq[-1].this.rhs.find(Mul ** Binomial).apply(Algebra.Pow.eq.Mul.split.base)

    Eq << Eq[-1].this.find(Symbol ** Add).find(Binomial).apply(Discrete.BinomAdd__2.eq.Add_Binom_2, d)




if __name__ == '__main__':
    run()
# created on 2022-07-11
