from util import *



@apply
def apply(given, index=None):
    (fn, *limits_e), *limits_f = given.of(All[Any])
    eqs = fn.of(And)

    if index is None:
        eqs = tuple(All(Any(eq, *limits_e), *limits_f) for eq in eqs)
        return eqs

    eq = eqs[index]

    return All(Any(eq, *limits_e), *limits_f)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    x, y, z, a, b = Symbol(real=True)

    f, g = Function(shape=(), real=True)

    Eq << apply(All[x:0:a](Any[y:0:b]((g(x, y, z) <= 1) & (f(x, y, z) >= 1))), index=0)

    Eq << Eq[0].this.expr.expr.apply(Logic.Cond.of.And, index=0)


if __name__ == '__main__':
    run()

# created on 2018-12-23
