from util import *


@apply
def apply(eq_M, x, w, r):
    (((i, (β0, ζ0)), (j, (β1, ζ1))), (S[j], S[0], n1), (S[i], S[0], n0), (k, S[0], m)), M = eq_M.of(Equal[Stack[Bool[Element[Range] & Element[Range]]]])

    β0, S[k] = β0.of(Indexed)
    ζ0, S[k] = ζ0.of(Indexed)

    β1, S[k] = β1.of(Indexed)
    ζ1, S[k] = ζ1.of(Indexed)


    S[m], S[n0], S[n1], d = x.shape
    l0, l1, S[d], d_ = w.shape

    t = Symbol(integer=True)
    M0 = Stack[t:d, j:n1, i:n0, k:m](M[k, i, j])
    M1 = Stack[t:d_, j:n1, i:n0, k:m](M[k, i, j])

    block = conv2d[r](x[k][β0[k]:ζ0[k], β1[k]:ζ1[k]], w)

    block = BlockMatrix[1](Zeros(ζ0[k] - β0[k], β1[k], d_), block, Zeros(ζ0[k] - β0[k], n1 - ζ1[k], d_))

    block = BlockMatrix(Zeros(β0[k], n1, d_), block, Zeros(n0 - ζ0[k], n1, d_))

    return Equal(conv2d[r](x * M0, w) * M1, Stack[k:m](block))


@prove(slow=True)
def prove(Eq):
    from Lemma import Set, Algebra, Logic, Tensor

    m, d, d_quote = Symbol(integer=True, positive=True)
    n, l, r = Symbol(shape=(2,), integer=True, positive=True)
    # r = dilation rate
    β0 = Symbol("β^0", shape=(m,), domain=Range(n[0]))
    ζ0 = Symbol("ζ^0", shape=(m,), domain=Range(1, n[0] + 1))
    β1 = Symbol("β^1", shape=(m,), domain=Range(n[1]))
    ζ1 = Symbol("ζ^1", shape=(m,), domain=Range(1, n[1] + 1))
    x = Symbol(real=True, shape=(m, n[0], n[1], d))
    w = Symbol(real=True, shape=(l[0], l[1], d, d_quote))
    M = Symbol(real=True, shape=(m, n[0], n[1]))
    i, j, k = Symbol(integer=True)
    Eq << apply(
        Equal(M, Stack[j:n[1], i:n[0], k:m](Bool(Element(i, Range(β0[k], ζ0[k])) & Element(j, Range(β1[k], ζ1[k]))))), x, w, r)

    Eq.M_def = Eq[0].this.find(Element).apply(Set.In_Range.Is.And).this.find(Element).apply(Set.In_Range.Is.And)

    Eq << Eq[-1].rhs.find(conv2d).this.defun()

    d0 = Symbol((l[0] - 1) // 2 * r[0] + (r[0] // 2) * (1 - l[0] % 2))
    Eq.mul_floor_0 = d0.this.definition.reversed.this.apply(Algebra.Eq.transport, lhs=0)

    d1 = Symbol((l[1] - 1) // 2 * r[1] + (r[1] // 2) * (1 - l[1] % 2))
    Eq.mul_floor_1 = d1.this.definition.reversed.this.apply(Algebra.Eq.transport, lhs=0)
    Eq.conv2d = Eq[-1].subs(Eq.mul_floor_0, Eq.mul_floor_1)

    C = Symbol(Eq[1].lhs)
    Eq << C.this.definition

    Eq << Eq[-1].this.find(conv2d).defun()

    Eq << Eq[-1].subs(Eq.mul_floor_0, Eq.mul_floor_1)

    Eq << Eq[-1][k, i, j]

    Eq << Eq[-1].this.find(Sum, Stack).subs(Eq.M_def)

    Eq << Eq[-1].this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].this.find(Piecewise).apply(Logic.Ite.nest, pivot=slice(1, None, 2))# select cond with j

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.separate.Ite)

    Eq << Eq[-1].this.find(Min, Add[Min]).apply(Algebra.Add.eq.Min).this.find(Min, Add[Min]).apply(Algebra.Add.eq.Min)

    Eq << Eq[-1].this.find(Min[Ceil]).apply(Algebra.Min.eq.Add, 1).this.find(Min[Ceil]).apply(Algebra.Min.eq.Add, 1)

    Eq << Eq[-1].this.find(Add[Ceil]).apply(Algebra.Add.Ceil.eq.Floor).this.find(Add[Ceil]).apply(Algebra.Add.Ceil.eq.Floor)

    Eq << Eq[-1].this.find(Min[Floor]).apply(Algebra.Min.eq.Floor).this.find(Min[Floor]).apply(Algebra.Min.eq.Floor)

    Eq << Eq[-1].this.find(-Floor).apply(Algebra.Mul.eq.Ceil).this.find(-Floor).apply(Algebra.Mul.eq.Ceil)

    Eq << Eq[-1].this.rhs.subs(Eq.M_def)

    Eq << Eq[-1].this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq.convolution_definition = Eq[-1].this.rhs.apply(Algebra.Mul.eq.Ite)

    C_quote = Symbol("C'", Eq[1].rhs)
    Eq << C_quote.this.definition

    Eq << Eq[-1][k]

    Eq << Eq[-1].this.rhs.subs(Eq.conv2d)

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.rhs.apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite)

    Eq << Eq[-1][j]

    Eq << Eq[-1].this.find(Piecewise, Piecewise).apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite)

    Eq << Eq[-1].this.rhs.apply(Logic.Ite_Ite.eq.Ite__Ite)

    Eq << Eq[-1].this.find(-Floor).apply(Algebra.Mul.eq.Ceil).this.find(-Floor).apply(Algebra.Mul.eq.Ceil)

    Eq << Eq[-1].this.find(-Add).apply(Algebra.Mul.distribute).this.find(-Add).apply(Algebra.Mul.distribute)

    Eq << Eq[-1].this.find(Min[Floor]).apply(Algebra.Min.eq.Floor).this.find(Min[Floor]).apply(Algebra.Min.eq.Floor)

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq.convolution_definition, Eq[-1])

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (j, 0, n[1]), (i, 0, n[0]), (k, 0, m))

    Eq << Eq[-1].subs(C.this.definition, C_quote.this.definition)





if __name__ == '__main__':
    run()
# created on 2021-01-01
# updated on 2023-06-01
