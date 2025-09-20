from util import *


@apply
def apply(given):
    function, *limits = given.of(Any)
    limits = [(x,) for x, *_ in limits]
    limits[0] = (limits[0][0], function)
    return Any(given.limits_cond, *limits)


@prove
def prove(Eq):
    from Lemma import Set
    S = Symbol(etype=dtype.real)
    e, t = Symbol(real=True)
    f, g = Function(shape=(), integer=True)

    Eq << apply(Any[e:g(e) > 0](f(e) > 0))

    A = Symbol(conditionset(e, g(e) > 0))
    B = Symbol(conditionset(e, f(e) > 0))

    Eq.A_definition = A.this.definition
    Eq.B_definition = B.this.definition

    Eq << Any[e:A](Element(e, B), plausible=True)

    Eq << Eq[-1].this.expr.rhs.definition

    Eq << Eq[-1].subs(Eq.A_definition)

    Eq << Set.Any_In.of.Any_In.limits.swap.apply(Eq[2], simplify=False)

    Eq << Eq[-1].this.expr.rhs.definition

    Eq << Eq[-1].subs(Eq.B_definition)


if __name__ == '__main__':
    run()

# created on 2020-09-05
