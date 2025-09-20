from util import *


@apply
def apply(given, P):
    f_gx, *limits = given.of(All)
    assert P.is_ConditionSet or P.definition.is_ConditionSet
    _, y, cond = P.image_set()
    pattern = cond._subs(y, Wild(y.name, **y.assumptions0), symbol=False)

    res = f_gx.match(pattern)
    gx, *_ = res.values()

    return given.func(Element(gx, P), *limits)


@prove
def prove(Eq):
    n, m = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    y = Symbol(complex=True, shape=(m,))
    A = Symbol(etype=dtype.complex[n])
    f = Function(shape=(), integer=True)
    g = Function(shape=(m,))
    P = Symbol(conditionset(y, Equal(f(y), 1)))
    Eq << apply(All[x:A](Equal(f(g(x)), 1)), P)

    Eq << Eq[-1].this.expr.rhs.definition


if __name__ == '__main__':
    run()
# created on 2021-08-20
