from util import *


@apply
def apply(eq):
    (H, (((((A, i), (S[0], S[i])), (S[i], S[0], (l, n))), (S[A[i + Min(l, n), i + 1:i + Min(l, n)]], (S[i], S[0], S[n - Min(l, n)]))), (((S[A[i]], (S[i], (S[i], (S[n], u)))), (S[i], S[0], S[n - Min(n, u)])), (S[A[i + n - Min(n, u), i + n - Min(n, u):]], (S[i], S[0], S[Min(n, u)])))), ((S[H[i]], S[A[i, relu(i - l + 1):Min(n, i + u)]]), (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[1][Zeros, Expr, Zeros] + BlockMatrix[1][
            BlockMatrix[
                Stack[
                    BlockMatrix[
                        NegativeInfinity * Ones,
                        Sliced[Indexed]
                    ],
                    Tuple[Min]
                ],
                Stack
            ],
            BlockMatrix[
                Stack[Sliced[Tuple[Add[Min]]]],
                Stack[
                    BlockMatrix[
                        NegativeInfinity * Ones
                    ]
                ]
            ]
        ] - Stack[Ones * Log[ReducedSum[Exp[Add[BlockMatrix[Zeros, Expr, Zeros]]]]]]])
    assert n >= 2 and u >= 2 and l >= 2
    breadth = Add(Min(l, n), Min(u, n), -1)
    return Equal(softmax(A + H * Identity(n) + (BandPart[l - 1, u - 1](Ones(n, n)) - 1) * oo),
                 BlockMatrix(
                    Stack[i:Min(l, n)](BlockMatrix(Exp(z[i, Min(l, n) - i - 1:Min(l, n) - 1]), Zeros(n - i))),
                    Stack[i:n - Min(l, n)](BlockMatrix(Zeros(i + 1), Exp(z[i + Min(l, n), :Min(l, n) - 1]), Zeros(n - i - Min(l, n))))
                 ) + BlockMatrix(
                    Stack[i:n - Min(u, n)](BlockMatrix(Zeros(i), Exp(z[i, Min(l, n) - 1:]), Zeros(n - i - Min(u, n)))),
                    Stack[i:Min(u, n)](BlockMatrix(Zeros(n - Min(u, n) + i), Exp(z[i + n - Min(u, n), Min(l, n) - 1:breadth - i])))
                 ))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Bool, Int, Nat

    n, l, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    H = Symbol(shape=(n,), real=True)
    breadth = Add(Min(l, n), Min(u, n), -1)
    z = Symbol(shape=(n, breadth), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix[1](Zeros(n, Min(l, n) - 1), H, Zeros(n, Min(u, n) - 1)) + BlockMatrix[1](
        BlockMatrix(
            Stack[i:Min(l, n)](BlockMatrix(-oo * Ones(Min(l, n) - i - 1), A[i, :i])),
            Stack[i:n - Min(l, n)](A[i + Min(l, n), i + 1:i + Min(l, n)])
        ),
        BlockMatrix(
            Stack[i:n - Min(u, n)](A[i, i:i + Min(u, n)]),
            Stack[i:Min(u, n)](BlockMatrix(A[i + n - Min(u, n), n - Min(u, n) + i:], -oo * Ones(i)))
        )) - Stack[i:n](Ones(breadth) * Log(ReducedSum(Exp(A[i, relu(i + 1 - l):Min(n, i + u)] + BlockMatrix(Zeros(i - relu(i - l + 1)), H[i], Zeros(-i + Min(n, i + u) - 1))))))))

    Eq << BlockMatrix[1](H, Zeros(n, Min(u, n) - 1)).this.apply(Algebra.Block.split, n - Min(u, n))

    Eq << Eq[0].find(BlockMatrix[1][Zeros]).this.subs(Eq[-1])

    Eq << Eq[0].subs(Eq[-1])

    Eq << Add(*Eq[-1].find(Add[BlockMatrix]).args[:2]).this.apply(Algebra.Add.Block.eq.Block)

    Eq << Eq[-1].this.rhs.find(Add[BlockMatrix]).apply(Algebra.Add.Block.eq.Block)

    Eq.z_def = Eq[-3].subs(Eq[-1])

    A = Symbol(Add(*Eq[1].lhs.arg.args[:2]))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def[i][:i]

    Eq.left_upper_part = Eq[-1].this.find(Stack)().expr.simplify()

    Eq << Eq.A_def[i + Min(l, n)][i + 1:i + Min(l, n)]

    Eq.left_lower_part = Eq[-1].this.find(Stack)().expr.simplify()

    Eq << Eq.A_def[i + n - Min(u, n)][i + n - Min(u, n):]

    Eq << Eq[-1].this.find(Mul[Stack]).apply(Tensor.Expr.eq.Stack, simplify=None)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Mul.Stack)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Block)

    Eq << Eq[-1].this.find(Mul[BlockMatrix]).apply(Algebra.Mul.eq.Block)

    Eq.matmul_subs_right = Eq[-1].this.apply(Int.EqAdd.Is.Eq_Sub, rhs=0).reversed

    Eq << Eq.z_def.rhs.find(BlockMatrix[1] + Stack[BlockMatrix]).this.args[0].apply(Tensor.Expr.eq.Stack, i)

    Eq << Eq[-1].this.rhs.apply(Tensor.Add_Stack.eq.Stack_Add)

    Eq << Eq[-1].this.rhs.subs(Eq.matmul_subs_right)

    Eq << Eq[-1].this.rhs.find(Add).apply(Tensor.Expr.eq.Stack)

    Eq << Eq[-1].this.rhs.find(-Piecewise).apply(Nat.Mul_Ite.eq.Ite_MulS)

    Eq << Eq[-1].this.rhs.find(Add).apply(Nat.AddIteS.eq.IteAnd)

    Eq << Eq[-1].this.find(Piecewise).apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, 1)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(Nat.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(Nat.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs.find(Piecewise).apply(Bool.Ite_Ite.eq.Ite__Ite)

    Eq.lower_part = Eq[-1].this.rhs.apply(Tensor.Stack.Ite.eq.Stack.Block)

    Eq << Eq.A_def[i]

    Eq << Bool.AllIn.of.All.apply(Eq[-1], (i, 0, n - Min(u, n)))

    Eq << Algebra.All.Eq.Slice.of.All_Eq.apply(Eq[-1], slice(i, i + Min(u, n)))

    Eq << Eq[-1].this.find(KroneckerDelta).apply(Algebra.Delta.offset, -i)

    Eq << Eq[-1].this.find(Mul).apply(Tensor.Expr.eq.Stack, simplify=None)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Mul.Stack)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Block)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Block)

    Eq << Tensor.EqStackS.of.All_Eq.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack.eq.Add)

    Eq.upper_part = Eq[-1].this.find(Stack[BlockMatrix]).apply(Tensor.Stack.Block.eq.Block.Stack)

    Eq << Eq.A_def[i][relu(i + 1 - l):Min(n, i + u)]

    Eq << Eq[-1].this.find(KroneckerDelta).apply(Algebra.Delta.offset, -i)

    Eq << Eq[-1].this.find(Mul[Stack]).apply(Tensor.Expr.eq.Stack, simplify=None)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Mul.Stack)

    Eq << Eq[-1].this.find(KroneckerDelta).apply(Algebra.Delta.offset, -relu(i + 1 - l) + i)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Block)

    Eq << Eq[-1].this.find(Mul[BlockMatrix]).apply(Algebra.Mul.eq.Block)

    Eq << Eq[-1].this.apply(Int.EqAdd.Is.Eq_Sub, rhs=1).reversed

    Eq << Eq.z_def.subs(Eq.left_upper_part.reversed, Eq.left_lower_part.reversed, Eq[-1], Eq.upper_part.reversed, Eq.lower_part)

    Eq << Tensor.Softmax.eq.AddBlockS.of.Eq_Sub_Stack_Mul_LogSumExp.apply(Eq[-1])

    Eq << Eq[-1].this.find(Symbol).definition




if __name__ == '__main__':
    run()
# created on 2022-03-14
# updated on 2022-03-15



