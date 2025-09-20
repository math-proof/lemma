from util import *


@apply
def apply(cond, exists):
    (fn, *limits_e), *limits_f = exists.of(All[Any])
    return All(Any(cond & fn, *limits_e), *limits_f)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, y = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    f, g = Function(integer=True)
    Eq << apply(f(x, y) > 0, All[y:B](Any[x:A]((g(x, y) > 0))))

    Eq << Eq[-1].this.expr.apply(Logic.Any_And.given.Any.All, index=0)

    Eq << Logic.All_And.given.All.All.apply(Eq[-1])

    Eq << Algebra.All.given.Cond.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-03-13
