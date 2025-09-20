from util import *


@apply
def apply(given):
    (fx, (x, cond)), fy = given.of(Equal[Cup[FiniteSet], FiniteSet])
    z = Wild('z', **x.type.dict)
    fx_ = fx._subs(x, z)
    values = fy.match(fx_)
    y = values[z]

    return Unequal(conditionset(y, cond._subs(x, y)), e.emptySet)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    x, y = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer, given=True)

    f, g = Function(shape=(), integer=True)

    Eq << apply(Equal(imageset(x, f(x), g(x) > 0), {f(y)}))

    A = Symbol(Eq[1].lhs)

    Eq.A_definition = A.this.definition

    Eq << imageset(x, f(x), A).this.subs(Eq.A_definition)

    Eq << Eq[-1].this.rhs.limits_subs(y, x)

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[-1], Eq[0])

    Eq << Eq[1].subs(Eq.A_definition.reversed)

    Eq << ~Eq[-1]

    Eq << Eq[-3].subs(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-04-05
