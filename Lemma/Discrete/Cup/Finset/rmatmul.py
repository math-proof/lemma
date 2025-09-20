from util import *


@apply
def apply(x, w=None, right=None, var=None):
    n = x.shape[0]
    i, j = Symbol(integer=True)
    if w is None:
        w = Symbol(Stack[j, i](SwapMatrix(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_SwapMatrix or w[i, j].definition.is_SwapMatrix

    if right:
        lhs = (x @ w[i, j]).cup_finiteset(var=var)
    else:
        lhs = (w[i, j] @ x).cup_finiteset(var=var)
    return Equal(lhs, x.cup_finiteset(var=var))


@prove
def prove(Eq):
    from Lemma import Discrete, Set, Tensor

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), integer=True)
    Eq << apply(x)

    i, j = Eq[0].lhs.indices
    k = Eq[1].lhs.variable.copy(domain=Range(n))
    Eq << Eq[0].lhs[k].this.definition

    Eq << (Eq[0].lhs[k] @ x).this.args[0].definition

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1].this(i).find(Element).simplify()
    Eq << Eq[-1].this(j).find(Element).simplify()

    Eq << Eq[-1].apply(Set.Eq.Cup.Finset.of.Eq, (k, 0, n))

    Eq << Eq[-1].this.find(Complement[Complement]).apply(Set.SDiff_SDiff.eq.UnionInter)

    Eq << Eq[-1].this(i, j).find(Unequal, Intersection).simplify()

    Eq << Eq[-1].this(i, j).find(NotSubset, Intersection).simplify()

    Eq << Eq[-1].this(i, j).find(Element[Intersection]).simplify()

    Eq << Eq[-1].this(i, j).find(Intersection).simplify()

    Eq << Eq[-1].this.rhs.args[1]().expr.find(Intersection).simplify()

    Eq << Eq[-1].this.lhs.apply(Set.Cup.limits.domain_defined)

    Eq << Eq[-1].this.rhs.limits_subs(Eq[-1].rhs.variable, i)

    Eq << Eq[-1].this.rhs.apply(Set.Cup.limits.domain_defined)




if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html

# created on 2020-07-25
# updated on 2022-01-08
