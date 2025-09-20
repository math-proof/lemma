from util import *


@apply
def apply(P):
    definition = P.definition
    assert definition.is_ConditionSet
    x = definition.variable

    return All[x:P](definition.condition & Element(x, definition.base_set))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    n, m = Symbol(integer=True, positive=True)
    x = Symbol(shape=(oo,), integer=True)

    f = Function(shape=(), integer=True)

    P = Symbol(conditionset(x[:n], f(x[:n]) > 0, CartesianSpace(Range(m), n)))
    Eq << apply(P)

    Eq << Logic.All.of.All_And.apply(Eq[-1])

    Eq << All[x[:n]:P](Element(x[:n], P), plausible=True)

    Eq << Eq[-1].simplify()

    Eq << Eq[-1].this.expr.rhs.definition


if __name__ == '__main__':
    run()

# created on 2020-08-12
