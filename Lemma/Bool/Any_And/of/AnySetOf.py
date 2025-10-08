from util import *


@apply
def apply(given):
    expr, (x, *_) = given.of(Any)
    cond = given.limits_cond
    assert not cond
    return Any[x]((expr & cond).simplify())


@prove
def prove(Eq):
    from Lemma import Set

    e = Symbol(real=True)
    f, g = Function(shape=(), integer=True)
    Eq << apply(Any[e:g(e) > 0](f(e) > 0))

    S = Symbol(conditionset(e, g(e) > 0))
    Eq << Any[e:S](f(e) > 0, plausible=True)

    Eq << Eq[-1].this.limits[0][1].definition

    Eq << Set.Any_And_In.of.Any.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.find(Element).rhs.definition




if __name__ == '__main__':
    run()

# created on 2018-02-16
# updated on 2023-05-19
