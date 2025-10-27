from util import *


@apply
def apply(eq):
    ((((((A, i), (S[0], S[i])), (S[i], S[0], (l, n))), (S[A[i + Min(l, n), i + 1:i + Min(l, n)]], (S[i], S[0], S[n - Min(l, n)]))), ((((S[A], S[i]), (S[i], (S[i], (S[n], u)))), (S[i], S[0], (S[n], S[-Min(n, u)]))), (((S[A], S[i + n - Min(n, u)]), (S[i + n - Min(n, u)], S[n])), (S[i], S[0], (S[n], S[u]))))), (S[A[i][relu(i - l + 1):Min(n, i + u)]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[BlockMatrix[1][
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
            Stack[Sliced[Indexed, Tuple[Add[Min]]], Tuple[Add]],
            Stack[
                BlockMatrix[
                    Sliced[Indexed],
                    NegativeInfinity * Ones
                    ],
                Tuple[Min]
                ]
            ]
        ] - Stack[Ones * Log[ReducedSum[Exp]]]])

    assert n >= 2 and l >= 2 and u >= 2
    return Imply(i < Min(l, n, n - Min(u, n)), Equal(z[i], BlockMatrix(-oo * Ones(Min(l, n) - i - 1), z[i, Min(l, n) - i - 1:]))), \
        Imply(Element(i, Range(n - Min(u, n), Min(l, n))), Equal(z[i], BlockMatrix(-oo * Ones(Min(l, n) - i - 1), z[i, Min(l, n) - i - 1:n + Min(l, n) - i - 1], -oo * Ones(Min(u, n) + i - n)))), \
        Imply(i >= Max(Min(l, n), n - Min(u, n)), Equal(z[i], BlockMatrix(z[i,:n + Min(l, n) - i - 1], -oo * Ones(Min(u, n) + i - n)))), \



@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Tensor, Nat

    n, l, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    breadth = Add(Min(l, n), Min(u, n), -1)
    z = Symbol(shape=(n, breadth), extended_real=True)
    Eq << apply(Equal(z, BlockMatrix[1](
        BlockMatrix(
            Stack[i:Min(l, n)](BlockMatrix(-oo * Ones(Min(l, n) - i - 1), A[i,:i])),
            Stack[i:n - Min(l, n)](A[i + Min(l, n), i + 1:i + Min(l, n)])),
        BlockMatrix(
        Stack[i:n - Min(u, n)](A[i, i:i + Min(u, n)]),
        Stack[i:Min(u, n)](BlockMatrix(A[i + n - Min(u, n), n - Min(u, n) + i:], -oo * Ones(i))))) - Stack[i:n](Ones(breadth) * Log(ReducedSum(Exp(A[i, relu(i + 1 - l):Min(n, i + u)]))))))

    Eq << Bool.Imp.given.All.apply(Eq[1])

    Eq.block1 = Algebra.All.given.All.limits.domain_defined.apply(Eq[-1])

    Eq.block2 = Bool.Imp.given.All.apply(Eq[2])

    Eq << Bool.Imp.given.All.apply(Eq[3])

    Eq.block3 = Algebra.All.given.All.limits.domain_defined.apply(Eq[-1])

    j = Symbol(integer=True)
    Eq <<= Eq.block1.this.expr.lhs.apply(Tensor.Expr.eq.Stack, j)

    Eq <<= Eq[-1].this.expr.rhs.apply(Tensor.Expr.eq.Stack, j)

    Eq.z_ij_def = Eq[0][i][j]

    Eq << Eq[-1].subs(Eq.z_ij_def)

    Eq << Eq[-1].this.expr.rhs.apply(Nat.Ite.eq.SubIte, Eq[-1].find(Log[ReducedSum[Exp]]))

    Eq << Eq[-1].this(i).expr.lhs.find(Symbol < Min).simplify()

    Eq << Eq[-1].this(i).expr.rhs.find(Symbol < Min).simplify()

    Eq << Eq[-1].this(i).expr.lhs.find(Symbol < Symbol - Min).simplify()

    Eq << Eq[-1].this(i).expr.rhs.find(Symbol < Symbol - Min).simplify()

    Eq << Eq[-1].this.expr.lhs.apply(Bool.Ite_Ite.eq.Ite__Ite)

    Eq << Eq[-1].this.expr.rhs.apply(Bool.Ite_Ite.eq.Ite__Ite)

    Eq << Eq[-1].this(i).find(And).simplify()

    Eq <<= Eq.block2.this.expr.lhs.apply(Tensor.Expr.eq.Stack, j)

    Eq <<= Eq[-1].this.expr.rhs.apply(Tensor.Expr.eq.Stack, j)

    Eq <<= Eq[-1].this.find(ExprCondPair[2]).cond.apply(Algebra.Lt.transport, rhs=slice(0, 4, 3))

    Eq << Eq[-1].subs(Eq.z_ij_def)

    Eq << Eq[-1].this.expr.rhs.apply(Nat.Ite.eq.SubIte, Eq[-1].find(Log[ReducedSum[Exp]]))

    Eq << Eq[-1].this(i).expr.lhs.find(Symbol < Min).simplify()

    Eq << Eq[-1].this(i).expr.rhs.find(Symbol < Min).simplify()

    Eq << Eq[-1].this(i).expr.lhs.find(Symbol < Symbol - Min).simplify()

    Eq << Eq[-1].this(i).expr.rhs.find(Symbol < Symbol - Min).simplify()

    Eq << Eq[-1].this.expr.lhs.apply(Bool.Ite_Ite.eq.Ite__Ite)

    Eq << Eq[-1].this.expr.rhs.apply(Bool.Ite_Ite.eq.Ite__Ite)

    Eq << Eq[-1].this(i).find(And).simplify()

    Eq << Eq[-1].this.find(Or[~Less]).apply(Algebra.Lt.transport, rhs=slice(0, 2))

    Eq << Eq[-1].this.find(Or).apply(Algebra.Or_Lt.Is.Lt.Max)

    Eq << Eq[-1].this().find(Max).simplify()

    Eq <<= Eq.block3.this.expr.lhs.apply(Tensor.Expr.eq.Stack, j)

    Eq <<= Eq[-1].this.expr.rhs.apply(Tensor.Expr.eq.Stack, j)

    Eq <<= Eq[-1].this.find(Less).apply(Algebra.Lt.transport, rhs=slice(0, 4, 3))

    Eq << Eq[-1].subs(Eq.z_ij_def)

    Eq << Eq[-1].this.expr.rhs.apply(Nat.Ite.eq.SubIte, Eq[-1].find(Log[ReducedSum[Exp]]))

    Eq << Eq[-1].this(i).expr.lhs.find(Symbol < Min).simplify()

    Eq << Eq[-1].this(i).expr.rhs.find(Symbol < Min).simplify()

    Eq << Eq[-1].this(i).expr.lhs.find(Symbol < Symbol - Min).simplify()

    Eq << Eq[-1].this(i).expr.rhs.find(Symbol < Symbol - Min).simplify()


    Eq << Eq[-1].this.expr.rhs.apply(Bool.Ite_Ite.eq.Ite__Ite)

    Eq << Eq[-1].this.find(And[Or]).simplify()

    Eq << Eq[-1].this.find(Or[~Less]).apply(Algebra.Lt.transport, rhs=slice(0, 2))

    Eq << Eq[-1].this.find(Or).apply(Algebra.Or_Lt.Is.Lt.Max)

    Eq << Eq[-1].this(i).find(Max).simplify()



if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-05-20


from . import tf
