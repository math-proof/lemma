from util import *


@apply
def apply(eq_relu, eq_min):
    ((i, l), limit_i), β = eq_relu.of(Equal[Stack[relu[Expr + 1 - Expr]]])
    ((n, (S[i], u)), S[limit_i]), ζ = eq_min.of(Equal[Stack[Min[Add]]])

    S[i], S[0], S[n] = limit_i

    return ζ[i] - β[i] <= Min(n, l + u - 1)



@prove
def prove(Eq):
    from Lemma import Tensor, Algebra

    n, l, u = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    β, ζ = Symbol(integer=True, shape=(n,))
    Eq << apply(Equal(β, Stack[i:n](relu(i - l + 1))), Equal(ζ, Stack[i:n](Min(i + u, n))))

    Eq << Eq[1] - Eq[0]

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.find(relu).apply(Tensor.Relu.eq.Add.Min)

    Eq << Add(*Eq[-1].rhs.args[:3]).this.apply(Algebra.Add.eq.Min)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Min)

    Eq << Eq[-1].this.find(Min[~Add]).apply(Algebra.Add.eq.Min)



    Eq << LessEqual(Eq[-1].rhs, Eq[2].rhs, plausible=True)

    Eq << Eq[-1].subs(Eq[-2].reversed)





if __name__ == '__main__':
    run()
# created on 2021-12-23
# updated on 2022-03-30
