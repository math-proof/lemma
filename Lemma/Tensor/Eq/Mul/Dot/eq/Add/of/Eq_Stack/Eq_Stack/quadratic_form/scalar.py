from util import *


@apply
def apply(eq_x, eq_a):
    (((x_r, (k_r, (r_relative, S[-k_r], S[k_r]))),
      (x_c, (k_c, (c_relative, S[-k_c], S[k_c]))),
      (x_l, (k_l, (l_relative, S[-k_l], S[k_l]))),
      (x_o, (k_o, (o_relative, S[-k_o], S[k_o]))),
      (x_p, (k_p, (p_relative, S[-k_p], S[k_p])))),
      j_limit, i_limit), x = eq_x.of(Equal[Stack[Matrix[Indexed[Symbol, Add[clip]], Indexed[Symbol, Add[clip]], Indexed[Symbol, Add[clip]], Indexed[Symbol, Add[clip]], Indexed[Symbol, Add[clip]]]]])

    j, S[0], n = j_limit
    i, S[0], S[n] = i_limit

    (r, S[j]), (S[r], S[i]) = r_relative.of(Indexed - Indexed)
    (c, S[j]), (S[c], S[i]) = c_relative.of(Indexed - Indexed)
    (l, S[j]), (S[l], S[i]) = l_relative.of(Indexed - Indexed)
    (o, S[j]), (S[o], S[i]) = o_relative.of(Indexed - Indexed)
    (p, S[j]), (S[p], S[i]) = p_relative.of(Indexed - Indexed)

    (((A, ((S[r_relative], d_r), h_r), ((S[c_relative], d_c), h_c), ((S[l_relative], d_l), h_l), ((S[o_relative], d_o), h_o), ((S[p_relative], d_p), h_p)), S[j_limit], S[i_limit]), C), a = eq_a.of(Equal[Stack[Indexed[Symbol, Min[(Abs + 1) // Symbol, Symbol - 1], Min[(Abs + 1) // Symbol, Symbol - 1], Min[(Abs + 1) // Symbol, Symbol - 1], Min[(Abs + 1) // Symbol, Symbol - 1], Min[(Abs + 1) // Symbol, Symbol - 1]]] * Expr])

    from Lemma.Tensor.Mul.Dot.eq.Add.quadratic_form import quadratic_form, reduced_sum
    return Equal(quadratic_form(x[i, j], a[i, j], doit=False), reduced_sum(x[i, j], a[i, j]))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor

    # n is the sequence lenth
    n = Symbol(integer=True, positive=True)
    # the follwoing parameters are advised to be equal to 3:
    # 0 means shorter distances, 1 means median-sized distances, 2 means long distances;
    h_r, h_c, h_l, h_o, h_p = Symbol(integer=True, positive=True) # is advised to be (3, 3, 3, 3, 3)
    # the follwoing parameters are used for divisors in mapping possibly large relative positions finite integers:
    d_r, d_c, d_l, d_o, d_p = Symbol(integer=True, positive=True) # is advised to be (2, 2, 3, 8, 16)
    # W_Γ is the attention between inputs in each dimension:
    # in this experiment, W_Γ is of shape (3, 3, 3, 3, 3, 32) in all 7776 parameters;
    W_Γ = Symbol("W^Γ", shape=(h_r, h_c, h_l, h_o, h_p, 32), real=True)
    Γ = Symbol(shape=(32,), real=True)
    a = Symbol(shape=(n, n, 32), real=True)
    x = Symbol(shape=(n, n, 5), real=True)
    i, j = Symbol(integer=True)
    r, c, l, o, p = Symbol(shape=(n,), integer=True)
    # longest clipping distances for each dimension
    k_r, k_c, k_l, k_o, k_p = Symbol(integer=True, positive=True)
    # positional embedding for each dimension
    w_r = Symbol("w^r", shape=(2 * k_r + 1,), real=True)
    w_c = Symbol("w^c", shape=(2 * k_c + 1,), real=True)
    w_l = Symbol("w^l", shape=(2 * k_l + 1,), real=True)
    w_o = Symbol("w^o", shape=(2 * k_o + 1,), real=True)
    w_p = Symbol("w^p", shape=(2 * k_p + 1,), real=True)
    Eq << apply(Equal(x, Stack[j:n, i:n](Matrix((w_r[k_r + clip(r[j] - r[i], -k_r, k_r)],
                                                      w_c[k_c + clip(c[j] - c[i], -k_c, k_c)],
                                                      w_l[k_l + clip(l[j] - l[i], -k_l, k_l)],
                                                      w_o[k_o + clip(o[j] - o[i], -k_o, k_o)],
                                                      w_p[k_p + clip(p[j] - p[i], -k_p, k_p)])))),
                Equal(a, Stack[j:n, i:n](W_Γ[Min((abs(r[j] - r[i]) + 1) // d_r, h_r - 1), Min((abs(c[j] - c[i]) + 1) // d_c, h_c - 1), Min((abs(l[j] - l[i]) + 1) // d_l, h_l - 1), Min((abs(o[j] - o[i]) + 1) // d_o, h_o - 1), Min((abs(p[j] - p[i]) + 1) // d_p, h_p - 1)]) * Γ))

    Eq << Eq[-1].this.lhs.find(Stack).apply(Tensor.Stack.eq.Matrix)

    c = Symbol(a[i, j])
    Eq << Eq[-1].subs(c.this.definition.reversed)

    Eq << Eq[-1].this.lhs.apply(Tensor.Mul.Dot.eq.Add.quadratic_form)





if __name__ == '__main__':
    run()
# created on 2022-03-15
# updated on 2022-03-16
