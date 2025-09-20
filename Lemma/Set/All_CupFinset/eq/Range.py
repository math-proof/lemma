from util import *


@apply
def apply(P):
    # P is condition set;
    definition = P.definition
    assert definition.is_ConditionSet
    x = definition.variable
    return All[x:P](definition.limits[0][1])


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x = Symbol(shape=(oo,), integer=True, nonnegative=True)
    P = Symbol(conditionset(x[:n], Equal(x[:n].cup_finiteset(), Range(n))))
    Eq << apply(P)

    Eq << All[x[:n]:P](Element(x[:n], P), plausible=True)

    Eq << Eq[-1].simplify()

    Eq << Eq[-1].this.expr.subs(Eq[0])


if __name__ == '__main__':
    run()

# created on 2020-07-02
