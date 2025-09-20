from util import *


@apply
def apply(given, index):
    (fn, *limits_e), *limits_f = given.of(All[Any])
    eqs, *limits = fn.of(All[And])

    return All(Any(All(eqs[index], *limits), *limits_e), *limits_f)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, y, z, a, b, c = Symbol(real=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(All[x:0:a](Any[y:0:b](All[z:0:c]((g(x, y, z) <= 1) & (f(x, y, z) >= 1)))), index=0)

    Eq << Eq[0].this.find(All).apply(Logic.All.All.of.All_And)

    Eq << Eq[-1].this.expr.apply(Algebra.AndAnyS.of.Any_And)

    Eq << Logic.All.of.All_And.apply(Eq[-1], index=0)


if __name__ == '__main__':
    run()

# created on 2018-12-25
