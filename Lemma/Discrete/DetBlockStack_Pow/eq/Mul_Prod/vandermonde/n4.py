from util import *


@apply
def apply(self):
    ((r, j), j_limit), ((S[j], (S[r], S[j])), S[j_limit]), ((S[j], (S[r], S[j])), S[j_limit]), ((S[j], (S[r], S[j])), S[j_limit]), ((S[j], i), S[j_limit], (S[i], S[0], n)) = self.of(Det[BlockMatrix[Stack[Pow], Stack[Symbol * Pow], Stack[Symbol ** 2 * Pow], Stack[Symbol ** 3 * Pow], Stack[Pow]]])

    S[j], S[0], S[n + 4:n > 0] = j_limit
    return Equal(self, 12 * r ** Binomial(4, 2) * (1 - r) ** (4 * n) * Product[j:n](factorial(j)))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor, Finset

    r = Symbol(real=True)
    n = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    Eq << apply(Det(BlockMatrix([Stack[j:n + 4](r ** j), Stack[j:n + 4](j * r ** j), Stack[j:n + 4](j ** 2 * r ** j), Stack[j:n + 4](j ** 3 * r ** j), Stack[j:n + 4, i:n](j ** i)])))

    # reference:
    # http://localhost/axiom/?module=Discrete.Det_Block.to.Mul.Prod.vandermonde.st.Lamda.Pow.n3
    j, i = Eq[0].lhs.arg.args[-1].variables
    E = Stack[j:n + 4, i:n + 4]((-1) ** (j - i) * binomial(j, i))
    Eq << (Eq[0].lhs.arg @ E).this.apply(Tensor.Dot.eq.Block)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].find(Stack[Sum, Tuple[2]]).this().expr.simplify()

    Eq << Eq[-1].this.rhs.expr.apply(Discrete.Sum.Binom.eq.Mul.Stirling, simplify=None)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Stack[Sum, Tuple])().expr.simplify()

    Eq << Eq[-1].this.rhs.args[1]().expr.simplify()

    Eq << Eq[-1].this.rhs.args[2]().expr.simplify()

    Eq << Eq[-1].this.rhs.args[3]().expr.simplify()

    Eq.eq_block = Eq[-1].this.find(Sum).apply(Discrete.Sum.Binom.eq.Pow.Newton)

    Eq << Eq.eq_block.rhs.args[1].expr.this.find(Pow).apply(Algebra.Pow.eq.Mul.split.exponent, simplify=None)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum_Mul.eq.Mul_Sum)

    Eq << Eq[-1].this.rhs.find(Sum).expr.apply(Algebra.Mul.simp.Pow.Mul.base)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Discrete.Sum.Binom.eq.Mul.Newton)

    Eq << Eq[-1].this.rhs.args[-1].apply(Algebra.Pow.eq.Mul.Neg)

    Eq.eq_block = Eq.eq_block.subs(Eq[-1])

    Eq << Eq.eq_block.rhs.args[2].expr.this.find(Pow).apply(Algebra.Pow.eq.Mul.split.exponent, simplify=None)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum_Mul.eq.Mul_Sum)

    Eq << Eq[-1].this.rhs.find(Sum).expr.apply(Algebra.Mul.simp.Pow.Mul.base)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Discrete.Sum.Binom.eq.Mul.Newton.deux)

    Eq << Eq[-1].this.find(Add ** Add).apply(Algebra.Pow.eq.Mul.Neg)

    Eq.eq_block = Eq.eq_block.subs(Eq[-1])

    Eq << Eq.eq_block.rhs.args[3].expr.this.find(Pow).apply(Algebra.Pow.eq.Mul.split.exponent, simplify=None)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum_Mul.eq.Mul_Sum)

    Eq << Eq[-1].this.rhs.find(Sum).expr.apply(Algebra.Mul.simp.Pow.Mul.base)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Discrete.Sum.Binom.eq.Mul.Newton.trois)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Add ** Add).apply(Algebra.Pow.eq.Mul.Neg)

    Eq << Eq[-1].this.find((1 - Symbol) ** Add).apply(Algebra.Pow.eq.Mul.Neg)

    Eq << Eq[-1].this.rhs.apply(Algebra.AddMulS.eq.Mul_Add)

    Eq << Eq.eq_block.subs(Eq[-1])

    Eq << ShiftMatrix(n + 4, 3, n + 3) @ Eq[-1]

    Eq << ShiftMatrix(n + 4, 2, n + 2) @ Eq[-1]

    Eq << ShiftMatrix(n + 4, 1, n + 1) @ Eq[-1]

    Eq << ShiftMatrix(n + 4, 0, n) @ Eq[-1]

    Eq << Eq[-1].this.rhs.args[0].apply(Tensor.Stack.eq.Block.split, n, axis=1)

    Eq << Eq[-1].this.rhs.args[1].apply(Tensor.Stack.eq.Block.split, n)

    Eq << Eq[-1].this.rhs.args[2].apply(Tensor.Stack.eq.Block.split, n)

    Eq << Eq[-1].this.rhs.args[3].apply(Tensor.Stack.eq.Block.split, n)

    Eq << Eq[-1].this.rhs.args[4].apply(Tensor.Stack.eq.Block.split, n)

    Eq << Eq[-1].this.rhs.args[0].args[1].apply(Tensor.Stack.doit.inner)

    Eq << Eq[-1].this.rhs.args[0].args[1]().expr.simplify()

    Eq << Eq[-1].this.rhs.args[1].args[1].apply(Tensor.Stack.eq.Matrix)

    Eq << Eq[-1].this.rhs.args[2].args[1].find(Stack).apply(Tensor.Stack.eq.Matrix)

    Eq << Eq[-1].this.rhs.args[3].args[1].find(Stack).apply(Tensor.Stack.eq.Matrix)

    Eq << Eq[-1].this.rhs.args[4].args[1].find(Stack).apply(Tensor.Stack.eq.Matrix)

    Eq << Eq[-1].this.find(Mul[Matrix]).apply(Discrete.Mul.eq.Matrix)

    Eq << Eq[-1].this.find(Mul[Matrix]).apply(Discrete.Mul.eq.Matrix)

    Eq << Eq[-1].this.find(Mul[Matrix]).apply(Discrete.Mul.eq.Matrix)

    Eq << Discrete.EqDet.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Discrete.Det.eq.Mul, deep=True)

    Eq << Eq[-1].this.rhs.apply(Discrete.Det.Block.eq.Mul)

    Eq << Eq[-1].this.find(Add ** Mul).apply(Algebra.Pow.eq.Mul.Neg)




if __name__ == '__main__':
    run()
# created on 2022-07-11
# updated on 2023-03-21
