from util import *


@apply
def apply(self):
    (((i, (b, (j, d))), (S[j], S[0])), (S[i / b ** ((j - 1) / d)], S[S.true])), (S[j], S[0], S[d]), (S[i], S[0], n) = self.of(Stack[Piecewise[ExprCondPair[sin[Expr * Expr ** (-Expr / Expr)], Equal[Expr % 2]], ExprCondPair[cos]]])
    j = Stack[j:d](j)
    return Equal(self, sin(S.Pi / 2 * (j % 2) + (Stack[i:n](i) * Ones(d, n)).T * exp(-2 * (j // 2) / d * log(b))))


@prove
def prove(Eq):
    from Lemma import Trigonometry, Algebra, Tensor

    n, b = Symbol(positive=True, integer=True)
    d = Symbol(integer=True, positive=True, even=True)
    i, j = Symbol(integer=True)
    Eq << apply(Stack[j:d, i:n](Piecewise((sin(i / b ** (j / d)), Equal(j % 2, 0)), (cos(i / b ** ((j - 1) / d)), True))))

    Eq << Eq[0].this.lhs.expr.apply(Trigonometry.Ite.eq.Sin.sinusoidal)

    i = Symbol(domain=Range(n))
    j = Symbol(domain=Range(d))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], (i, j))

    Eq << Trigonometry.Eq_Sin.given.Eq.apply(Eq[-1])
    Eq << Eq[-1].this.find(Mul[Log]).apply(Algebra.Mul.eq.Log)



if __name__ == '__main__':
    run()
# created on 2022-01-23
