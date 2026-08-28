from util import *


@apply
def apply(self):
    ((r, j), j_limit), ((S[j], (S[r], S[j])), S[j_limit]), ((S[j], (S[r], S[j])), S[j_limit]), ((S[j], i), S[j_limit], (S[i], S[0], n)) = self.of(Det[BlockMatrix[Stack[Pow], Stack[Symbol * Pow], Stack[Symbol ** 2 * Pow], Stack[Pow]]])

    S[j], S[0], S[n + 3:n > 0] = j_limit

    return Equal(self, 2 * r ** 3 * (1 - r) ** (3 * n) * Product[j:n](factorial(j)))


@prove
def prove(Eq):
    from Lemma import Finset, Tensor, Real, Int, Nat

    r = Symbol(real=True)
    n = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    Eq << apply(Det(BlockMatrix([Stack[j:n + 3](r ** j), Stack[j:n + 3](j * r ** j), Stack[j:n + 3](j ** 2 * r ** j), Stack[j:n + 3, i:n](j ** i)])))

    # reference:
    # http://localhost/axiom/?module=Finset.Det_Block.to.Mul.Prod.vandermonde.st.Lamda.Pow.n2
    j, i = Eq[0].lhs.arg.args[-1].variables
    E = Stack[j:n + 3, i:n + 3]((-1) ** (j - i) * binomial(j, i))
    Eq << (Eq[0].lhs.arg @ E).this.apply(Tensor.DotAppendS.eq.AppendAddSDotS)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].find(Stack[Sum, Tuple[2]]).this().expr.simplify()

    Eq << Eq[-1].this.rhs.expr.apply(Finset.Sum.Binom.eq.Mul.Stirling, simplify=None)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Stack[Sum, Tuple])().expr.simplify()

    Eq << Eq[-1].this.rhs.args[1]().expr.simplify()

    Eq << Eq[-1].this.rhs.args[2]().expr.simplify()

    Eq.eq_block = Eq[-1].this.find(Sum).apply(Finset.Sum.Binom.eq.Pow.Newton)

    Eq << Eq.eq_block.rhs.args[1].expr.this.find(Pow).apply(Real.Pow_Add.eq.MulPowS.of.Gt_0, simplify=None)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum_Mul.eq.Mul_Sum)

    Eq << Eq[-1].this.rhs.find(Sum).expr.apply(Nat.Mul.simp.Pow.Mul.base)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Finset.Sum.Binom.eq.Mul.Newton)

    Eq << Eq[-1].this.rhs.args[-1].apply(Int.Pow.eq.Mul.Neg)

    Eq.eq_block = Eq.eq_block.subs(Eq[-1])

    Eq << Eq.eq_block.rhs.args[2].expr.this.find(Pow).apply(Real.Pow_Add.eq.MulPowS.of.Gt_0, simplify=None)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum_Mul.eq.Mul_Sum)

    Eq << Eq[-1].this.rhs.find(Sum).expr.apply(Nat.Mul.simp.Pow.Mul.base)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Finset.Sum.Binom.eq.Mul.Newton.deux)

    Eq << Eq[-1].this.find(Add ** Add).apply(Int.Pow.eq.Mul.Neg)

    Eq << Eq.eq_block.subs(Eq[-1])

    Eq << ShiftMatrix(n + 3, 2, n + 2) @ Eq[-1]

    Eq << ShiftMatrix(n + 3, 1, n + 1) @ Eq[-1]

    Eq << ShiftMatrix(n + 3, 0, n) @ Eq[-1]

    Eq << Eq[-1].this.rhs.args[0].apply(Tensor.Stack.eq.Block.split, n, axis=1)

    Eq << Eq[-1].this.rhs.args[1].apply(Tensor.Stack.eq.Block.split, n)

    Eq << Eq[-1].this.rhs.args[2].apply(Tensor.Stack.eq.Block.split, n)

    Eq << Eq[-1].this.rhs.args[3].apply(Tensor.Stack.eq.Block.split, n)

    Eq << Eq[-1].this.rhs.args[0].args[1].apply(Tensor.Stack.doit.inner)

    Eq << Eq[-1].this.rhs.args[0].args[1]().expr.simplify()

    Eq << Eq[-1].this.rhs.args[1].args[1].apply(Tensor.Stack.eq.Tensor)

    Eq << Eq[-1].this.rhs.args[2].args[1].find(Stack).apply(Tensor.Stack.eq.Tensor)

    Eq << Eq[-1].this.rhs.args[3].args[1].find(Stack).apply(Tensor.Stack.eq.Tensor)

    Eq << Eq[-1].this.find(Mul[Matrix]).apply(Tensor.Mul.eq.Tensor)

    Eq << Eq[-1].this.find(Mul[Matrix]).apply(Tensor.Mul.eq.Tensor)

    Eq << Finset.EqDet.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Finset.Det.eq.Mul)

    Eq << Eq[-1].this.rhs.apply(Finset.Det.Block.eq.Mul)

    Eq << Eq[-1].this.find(Mul[Add ** Add]).powsimp()

    Eq << Eq[-1].this.find(Mul[Add ** Add]).powsimp()

    Eq << Eq[-1].this.find(Mul[Add ** Add]).powsimp()

    Eq << Eq[-1].this.find(Mul[Add ** Add]).powsimp()

    Eq << Eq[-1].this.find(Mul[Add ** Add]).powsimp()

    Eq << Eq[-1].rhs.args[0].this.apply(Int.AddAddS.eq.MulAddS)

    Eq << Eq[-1].this.rhs.args[-1].expand()

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.find(Add ** Mul).apply(Int.Pow.eq.Mul.Neg)




if __name__ == '__main__':
    run()
# created on 2022-07-11
