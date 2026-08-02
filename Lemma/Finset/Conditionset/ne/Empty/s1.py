from util import *


@apply
def apply(n, k=None):
    from sympy.functions.combinatorial.numbers import Stirling
    if k is None:
        k = Symbol(domain=Range(1, n + 1))
    assert k <= n and k > 0
    x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
    s = Stirling.conditionset(n, k, x)
    return Unequal(s, s.etype.emptySet)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    n = Symbol(integer=True, positive=True, given=True)
    k = Symbol(domain=Range(1, n + 1), given=True)
    Eq << apply(n, k=k)

    Eq << Set.Ne_Empty.given.Any.split.Conditionset.apply(Eq[0])

    i = Symbol(integer=True)
    x, (_, k), *_ = Eq[-1].variable.args
    a = Symbol(Stack[i:k](Piecewise((Range(k - 1, n), Equal(i, k - 1)), (i.set, True))))
    Eq << Algebra.Any.given.Cond.subst.apply(Eq[-1], x[:k], a)

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1], 1)

    Eq << Eq[-2].this.find(Indexed).definition

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq << Eq[-2].this.find(Indexed).definition

    Eq << Eq[-1].this.find(Indexed).definition


if __name__ == '__main__':
    run()
# created on 2020-11-08
