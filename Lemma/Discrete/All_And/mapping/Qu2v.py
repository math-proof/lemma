from util import *


@apply
def apply(n, u, v):
    Q, w, x = predefined_symbols(n)
    X, index = X_definition(n, w, x)
    return All[x[:n + 1]:Q[u]](Element(X[v], Q[v]) & Equal(x[:n + 1], w[n, index[u](X[v])] @ X[v]))


def X_definition(n, w, x):
    from Lemma.Discrete.And.of.Eq.index import index_function
    j = Symbol(integer=True)

    index = index_function(n + 1)
    return Symbol('X', Stack[j:n + 1](w[n, index[j](x[:n + 1], evaluate=False)] @ x[:n + 1])), index


def predefined_symbols(n):
    x = Symbol(shape=(oo,), integer=True, nonnegative=True)
    t, i, j = Symbol(integer=True)
    Q = Symbol(Stack[t:n + 1](conditionset(x[:n + 1], Equal(x[:n + 1].cup_finiteset(), Range(n + 1)) & Equal(x[n], t))))
    w = Symbol(Stack[j, i](SwapMatrix(n + 1, i, j)))

    return Q, w, x


@prove(proved=False)
def prove(Eq):
    from Lemma import Set, Algebra, Discrete, Logic, Tensor

    n = Symbol(integer=True, positive=True, given=True)
    u = Symbol(domain=Range(n + 1), given=True)
    v = Symbol(domain=Range(n + 1))
    Eq << apply(n, u, v)

    w, i, j = Eq[0].lhs.args
    Q = Eq[2].lhs.base
    Eq << Set.All_CupFinset.eq.Ico.apply(Q[u])

    Eq.x_slice_last, Eq.x_slice_domain = Logic.All.All.of.All_And.apply(Eq[-1])

    Eq << Eq.x_slice_domain.this.expr.apply(Discrete.And.of.Eq.index, v)

    Eq.h_domain, Eq.x_h_equality = Logic.All.All.of.All_And.apply(Eq[-1])

    hv = Eq.x_h_equality.expr.lhs.indices[0]
    Eq << Tensor.All_InDot.permutation.apply(n + 1, w=w)

    Eq << Subset(Eq[-2].limits[0][1], Eq[-1].rhs, plausible=True)

    Eq << Set.All.of.Subset.All.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].subs(Eq[-1].rhs.this.definition)

    Eq << Eq[-1].this.expr.simplify()

    Eq << Eq[-1].subs(i, n)

    Eq << Eq[-1].subs(j, hv)

    k = Eq[-1].expr.lhs.expr.arg.args[0].indices[-1]
    Eq.Xv_definition = Eq[1].subs(j, v)

    Eq << Eq.Xv_definition[k].apply(Set.Eq.Cup.Finset.of.Eq, (k, 0, n + 1))

    Eq.x_n1_cup_finiteset = Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq.Xv_definition[n]

    Eq << Eq[0].subs(i, n).subs(j, hv)[n]

    Eq << Eq[-2].this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.expand()

    Eq << Algebra.All.of.All_Eq.Cond.subst.apply(Eq.x_h_equality, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-07-26
