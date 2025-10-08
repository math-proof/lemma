from util import *


@apply
def apply(imply):
    from Lemma.Bool.Or_Not.of.All import rewrite_as_Or
    return rewrite_as_Or(imply)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    x = Symbol(integer=True)
    f = Function(shape=(), integer=True)
    A = Symbol(etype=dtype.integer, given=True)

    Eq << apply(All[x:A](f(x) > 0))

    Eq << ~Eq[0]

    Eq << Bool.Any_And.of.AnySetOf.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Bool.Bool.eq.One.of.Cond, split=False)

    Eq << Bool.BoolNot.eq.Zero.of.Cond.apply(Eq[1])

    Eq << Eq[-2].this.expr.apply(Bool.Eq.of.Eq.Eq, Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-02-17
