from util import *


@apply
def apply(exists, ou):
    fx, *limits_x = exists.of(Any)
    cond = fx.invert()
    [*eqs] = ou.of(Or)
    for i, eq in enumerate(eqs):
        if eq == cond:
            del eqs[i]
            return Or(*eqs)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, y = Symbol(real=True)
    A = Symbol(etype=dtype.real)
    f, g = Function(integer=True)
    Eq << apply(Any[x:A](f(x, y) > 0), (g(y, x) > 0) | (f(x, y) <= 0))

    Eq <<= Eq[0] & Eq[1]

    Eq << Logic.OrAndS.of.And_Or.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.args[1].apply(Logic.Any_And.of.Any.All)

    Eq << Logic.Cond.of.And.apply(Eq[-1], index=0)




if __name__ == '__main__':
    run()

# created on 2019-02-21
# updated on 2023-05-14

