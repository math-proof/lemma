from util import *


@apply
def apply(eq_M, x, w, r):
    ((i, (β, ζ)), (S[i], S[0], n), (k, S[0], m)), M = eq_M.of(Equal[Stack[Bool[Element[Range]]]])

    β, S[k] = β.of(Indexed)
    ζ, S[k] = ζ.of(Indexed)

    S[m], S[n], d = x.shape
    l, S[d], d_ = w.shape

    j = Symbol(integer=True)
    M0 = Stack[j:d, i:n, k:m](M[k, i])
    M1 = Stack[j:d_, i:n, k:m](M[k, i])

    return Equal(conv1d[r](x * M0, w) * M1, Stack[k:m](BlockMatrix(Zeros(β[k], d_),
                                                                   conv1d[r](x[k][β[k]:ζ[k]], w),
                                                                   Zeros(n - ζ[k], d_))))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic, Tensor

    m, n, d, d_quote, l, r = Symbol(integer=True, positive=True)
    # r is the dilation rate
    β = Symbol(shape=(m,), domain=Range(n))
    ζ = Symbol(shape=(m,), domain=Range(1, n + 1))
    x = Symbol(real=True, shape=(m, n, d))
    w = Symbol(real=True, shape=(l, d, d_quote))
    M = Symbol(real=True, shape=(m, n))
    i, k = Symbol(integer=True)
    Eq << apply(Equal(M, Stack[i:n, k:m](Bool(Element(i, Range(β[k], ζ[k]))))), x, w, r)

    Eq.M_def = Eq[0].this.find(Element).apply(Set.In_Range.Is.And)

    Eq << Eq[-1].rhs.expr.args[1].this.defun()

    d0 = Symbol((l - 1) // 2 * r + (r // 2) * (1 - l % 2))
    Eq.mul_floor = d0.this.definition.reversed.this.apply(Algebra.Eq.transport, lhs=0)

    Eq.conv1d = Eq[-1].subs(Eq.mul_floor)

    C = Symbol(Eq[1].lhs)
    Eq << C.this.definition

    Eq << Eq[-1].this.find(conv1d).defun()

    Eq << Eq[-1].subs(Eq.mul_floor)

    Eq << Eq[-1][k, i]

    Eq << Eq[-1].this.find(Sum, Stack).subs(Eq.M_def)

    Eq << Eq[-1].this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].this.find(Min, Add).apply(Algebra.Add.eq.Min)

    Eq << Eq[-1].this.find(Min).apply(Algebra.Min.eq.Add, 1)

    Eq << Eq[-1].this.find(Add[Ceil]).apply(Algebra.Add.Ceil.eq.Floor)

    Eq << Eq[-1].this.find(Min[Floor]).apply(Algebra.Min.eq.Floor)

    Eq << Eq[-1].this.find(-Floor).apply(Algebra.Mul.eq.Ceil)

    Eq << Eq[-1].this.rhs.subs(Eq.M_def)

    Eq << Eq[-1].this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq.convolution_definition = Eq[-1].this.rhs.apply(Algebra.Mul.eq.Ite)

    C_quote = Symbol("C'", Eq[1].rhs)
    Eq << C_quote.this.definition

    Eq << Eq[-1][k]

    Eq << Eq[-1].this.rhs.subs(Eq.conv1d)

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.rhs.apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite)

    Eq << Eq[-1].this.find(-Floor).apply(Algebra.Mul.eq.Ceil)

    Eq << Eq[-1].this.find(-Add).apply(Algebra.Mul.distribute)

    Eq << Eq[-1].this.find(Min[Floor]).apply(Algebra.Min.eq.Floor)

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq.convolution_definition, Eq[-1])

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (i, 0, n), (k, 0, m))

    Eq << Eq[-1].subs(C.this.definition, C_quote.this.definition)

    # https://arxiv.org/pdf/1408.5882.pdf




if __name__ == '__main__':
    run()
# created on 2021-01-01
# updated on 2023-12-17
