from util import *


@apply
def apply(eq_F, eq_F_quote):
    ((((i, (b, (j, d))), (S[j], S[0])), (S[i / b ** ((j - 1) / d)], S[S.true])), j_limit, i_limit), F = eq_F.of(Equal[Stack[Piecewise[ExprCondPair[cos[Expr * Expr ** (-Expr / Expr)], Equal[Expr % 2]], ExprCondPair[cos]]]])
    (((S[i / b ** (j / d)], (S[j], S[0])), (S[i / b ** ((j - 1) / d)], S[S.true])), S[j_limit], S[i_limit]), F_quote = eq_F_quote.of(Equal[Stack[Piecewise[ExprCondPair[sin, Equal[Expr % 2]], ExprCondPair[sin]]]])
    S[j], S[0], S[d] = j_limit
    S[i], S[0], n = i_limit

    return Equal(abs(F - S.ImaginaryUnit * F_quote), Ones(*F.shape))


@prove
def prove(Eq):
    from Lemma import Algebra, Trigonometry, Tensor, Nat

    n, b = Symbol(positive=True, integer=True)
    d = Symbol(integer=True, positive=True, even=True)
    F, F_quote = Symbol(real=True, shape=(n, d))
    i, j = Symbol(integer=True)
    Eq << apply(
        Equal(F, Stack[j:d, i:n](Piecewise((cos(i / b ** (j / d)), Equal(j % 2, 0)), (cos(i / b ** ((j - 1) / d)), True)))),
        Equal(F_quote, Stack[j:d, i:n](Piecewise((sin(i / b ** (j / d)), Equal(j % 2, 0)), (sin(i / b ** ((j - 1) / d)), True)))))

    Eq << Eq[2].subs(Eq[0], Eq[1])

    Eq << Eq[-1].this.find(Stack ** 2).apply(Tensor.Pow.eq.Stack)

    Eq << Eq[-1].this.find(Stack ** 2).apply(Tensor.Pow.eq.Stack)

    Eq << Eq[-1].this.find(Add).apply(Tensor.Add_Stack.eq.Stack_Add)

    Eq << Eq[-1].this.find(Add).apply(Nat.AddIteS.eq.IteAnd)

    Eq << Eq[-1].this.find(Cos ** 2).apply(Trigonometry.Square.Cos.eq.Sub.Square.Sin, simplify=None)

    Eq << Eq[-1].this.find(Cos ** 2).apply(Trigonometry.Square.Cos.eq.Sub.Square.Sin)





if __name__ == '__main__':
    run()
# created on 2021-12-14
# updated on 2023-11-26
