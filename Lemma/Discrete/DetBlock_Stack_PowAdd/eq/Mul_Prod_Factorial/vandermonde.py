from util import *


@apply
def apply(self):
    ((r, j1), (j, S[0], n)), ((S[j + 1], i1), (S[j], S[0], S[n]), (i, S[0], S[n - 1])) = self.of(Det[BlockMatrix[1 - Stack[Pow], Stack[Pow]]])

    assert j1 == j + 1
    assert i1 == i + 1

    return Equal(self, (1 - r) ** n * Product[i:n](factorial(i)))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Set, Tensor

    r = Symbol(real=True)
    n = Symbol(domain=Range(2, oo))
    i, j = Symbol(integer=True)
    Eq << apply(Det(BlockMatrix([1 - Stack[j:n](r ** (j + 1)), Stack[j:n, i:n - 1]((j + 1) ** (i + 1))])))

    Eq << Discrete.DetBlock_Stack_Pow.eq.Mul_Prod_Factorial.vandermonde.apply(Det(BlockMatrix([Stack[j:n + 1](r ** j), Stack[j:n + 1, i:n](j ** i)])))

    Eq << Eq[-1].lhs.arg.this.args[1].apply(Discrete.Stack.eq.Block.split, 1)

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], SwapMatrix(n + 1, 0, 1))

    Eq << Eq[-1].this.rhs.args[0].apply(Algebra.One.eq.Block, 1)

    Eq << Eq[-1].this.rhs.args[1].apply(Tensor.Stack.eq.Block.split, 1)

    Eq << Eq[-1].this.rhs.args[2].apply(Tensor.Stack.eq.Transpose.Block, 1)

    Eq << Eq[-1].this.find(Stack[Zero ** Add])().expr.simplify()

    Eq << Eq[-1] @ MulMatrix(n + 1, 0, -1)

    Eq.Dot = Eq[-1] @ (Identity(n + 1) + Stack[j:n + 1, i:n + 1]((1 - KroneckerDelta(j, 0)) * KroneckerDelta(i, 0)))

    Eq << Tensor.Add_Stack.eq.Stack_Add.apply(Eq.Dot.rhs.args[1])

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack.eq.Block.shift)

    Eq << Eq[-1].this.rhs.args[0].apply(Algebra.One.eq.Block, 1)

    Eq << Eq[-1].this.rhs.args[0].args[1].apply(Algebra.One.eq.Block, 1)

    Eq << Eq[-1].this.rhs.args[1].apply(Tensor.Stack.eq.Transpose.Block, 1)

    Eq << Eq[-1].this.rhs.args[1].args[1].apply(Tensor.Stack.eq.Block.split, 1, axis=1)

    Eq << Eq.Dot.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Block, deep=True)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1].this.find(Sum).expr.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.find(Sum).expr.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InSub, 1)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.find(Sum).expr.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InSub, 1)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.find(Sum).expr.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InSub, 1)

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.Block.eq.Block)

    Eq << Eq[-1].this.find(Add[BlockMatrix]).apply(Algebra.Add.eq.Block)

    Eq << Eq[-1].this.find(Add[BlockMatrix]).apply(Algebra.Add.eq.Block)

    Eq << MulMatrix(n + 1, 1, -1) @ (MulMatrix(n + 1, 0, -1) @ Eq[-1])

    Eq << Discrete.EqDet.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Discrete.Det.eq.Mul).reversed.subs(Eq[1])

    Eq << Eq[0].find(1 - Stack).this.apply(Tensor.Add_Stack.eq.Stack_Add)

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack.eq.Block.shift)

    Eq << Eq[-1].this.find(Stack[Add]).apply(Tensor.Stack.eq.Add)

    Eq << Eq[-4].subs(Eq[-1].reversed)

    Eq << Eq[0].find(Stack[Tuple[2]]).this.apply(Tensor.Stack.eq.Transpose.Block, 1)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Zeros(n).this.apply(Algebra.Expr.eq.Block, 1)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.lhs.apply(Discrete.Det.Block.eq.Mul)





if __name__ == '__main__':
    run()
# created on 2020-10-14
# updated on 2023-04-29

