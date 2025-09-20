from util import *


@apply
def apply(n, u=None):
    from Lemma.Discrete.All_And.mapping.Qu2v import predefined_symbols
    Q, *_ = predefined_symbols(n)
    if u is None:
        u = Q.definition.variable
    return Unequal(Q[u], Q[u].etype.emptySet)


@prove
def prove(Eq):
    from Lemma import Discrete, Set, Algebra, Tensor, Logic

    n = Symbol(integer=True, positive=True, given=True)
    Eq << apply(n)

    i = Symbol(integer=True)
    Q, t = Eq[0].lhs.args
    _t = t.copy(domain=Range(n + 1))
    a = Symbol(Stack[i:n + 1](i) @ SwapMatrix(n + 1, n, _t))
    Eq << a.this.definition

    Eq << a[n].this.definition.this.rhs.apply(Tensor.Dot.eq.Sum)

    Eq << Tensor.Cup.Finset.Dot.apply(a)

    Eq << Eq[-1].this.lhs.apply(Set.Cup.limits.domain_defined)

    Eq <<= Eq[-1] & Eq[-3]

    x = Eq[0].rhs.variable.base
    Eq.plausible = Any[x[:n + 1]](Element(x[:n + 1], Q[_t]), plausible=True)

    Eq << Eq.plausible.this.expr.rhs.definition

    Eq << Algebra.Any.given.Any.subst.apply(Eq[-1], x[:n + 1], a, simplify=None)

    Eq << Algebra.Any.given.Cond.apply(Eq[-1])

    Eq << Eq[-1].this.find(Element).apply(Set.In.given.Subset.Cup.Finset)

    Eq << Eq[-1].this.args[1:].apply(Algebra.Eq.Ufn.given.Eq.Ufn)

    Eq << Set.Ne_Empty.of.Any_In.apply(Eq.plausible)

    Eq << Logic.All.of.Cond.apply(Eq[-1], _t)





if __name__ == '__main__':
    run()
# created on 2020-11-07
# updated on 2023-08-26
