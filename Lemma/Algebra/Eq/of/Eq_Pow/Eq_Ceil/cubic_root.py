from util import *


def cubic_root(A):
    res = A.of(Expr ** 3)
    if res is not None:
        return res

    args = []
    for arg in A.of(Mul):
        if arg.is_Pow:
            args.append(arg.of(Expr ** 3))
        elif arg.is_Rational:
            p, q = arg.p, arg.q
            if p < 0:
                p = -p
                p = p ** (S.One / 3)
                p = -p
            elif p == 1:
                ...
            else:
                p = p ** (S.One / 3)

            if not p.is_integer:
                return

            q = q ** (S.One / 3)

            if not q.is_integer:
                return

            args.append(Rational(p, q))
        else:
            return
    return Mul(*args)


@apply
def apply(eq_pow, eq_ceiling):
    A, B = eq_pow.of(Equal)

    A = cubic_root(A)
    B = cubic_root(B)

    A_, B_ = eq_ceiling.of(Equal[Ceil, Ceil])
    (k, A_), b = A_.of(Expr * Arg - Expr)
    (S[k], B_), S[b] = B_.of(Expr * Arg - Expr)
    assert k == 3 / (S.Pi * 2)
    assert b == S.One / 2
    assert A_ == Arg(A).arg
    assert B_ == Arg(B).arg
    return Equal(A, B)


@prove
def prove(Eq):
    from Lemma import Algebra, Real, Nat

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Equal(A ** 3, B ** 3), Equal(Ceil(3 * Arg(A) / (S.Pi * 2) - S.One / 2), Ceil(3 * Arg(B) / (S.Pi * 2) - S.One / 2)))

    Eq << Eq[-1].this.lhs.apply(Algebra.Expr.eq.MulAbs_ExpMulIArg)

    Eq << Eq[-1].this.rhs.apply(Algebra.Expr.eq.MulAbs_ExpMulIArg)

    Eq << Nat.EqPowS.of.Eq.apply(Eq[0], exp=S.One / 3)

    Eq << Eq[-1].this.lhs.apply(Algebra.Root.eq.Mul.ExpI.Arg)

    Eq << Eq[-1].this.rhs.apply(Algebra.Root.eq.Mul.ExpI.Arg)

    Eq << Eq[-1].this.lhs.find(Arg).apply(Algebra.Arg.Pow.eq.Add)

    Eq << Eq[-1].this.rhs.find(Arg).apply(Algebra.Arg.Pow.eq.Add)

    Eq << Eq[-1].this.lhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.lhs.find(Exp).apply(Real.ExpAdd.eq.MulExpS)

    Eq << Eq[-1].this.rhs.find(Exp).apply(Real.ExpAdd.eq.MulExpS)

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq[-1] / Eq[-1].lhs.args[-1]


if __name__ == '__main__':
    run()
# created on 2019-04-26
