from util import *


@apply
def apply(given):
    from Lemma.Set.Eq.given.Eq.Cup.Finset import of_cup_finiteset
    cup_finiteset_abs, n = given.of(Equal)
    cup_finiteset = cup_finiteset_abs.of(Card)
    a = of_cup_finiteset(cup_finiteset)

    assert a.shape == (n,)

    k, i = Symbol(integer=True)

    p = Symbol(shape=(oo,), **a.dtype.dict)

    P = Symbol(conditionset(p[:n], Equal(p[:n].cup_finiteset(), cup_finiteset)))

    b = Symbol(integer=True, shape=(oo,), nonnegative=True)

    d = Symbol(Stack[i:n](i) @ MatProduct[i:n](SwapMatrix(n, i, b[i])))
    return All[p[:n]:P](Any[b[:n]](Equal(p[:n], Stack[k:n](a[d[k]]))))


@prove(proved=False)
def prove(Eq):
    from Lemma import Algebra, Set, Discrete

    n = Symbol(domain=Range(2, oo), given=False)
    a = Symbol(shape=(oo,), etype=dtype.integer, given=True)
    Eq << apply(Equal(Card(a[:n].cup_finiteset()), n))

    p = Eq[3].variable.base
    b = Eq[3].expr.variable.base
    Eq.hypothesis = Eq[3].subs(Eq[2]).copy(plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 2)

    Eq << Eq.initial.this.expr.expr.rhs.expr.indices[0].definition

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.Matrix)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.Matrix)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.Matrix)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.Matrix)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.Matrix)



if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-11-01
