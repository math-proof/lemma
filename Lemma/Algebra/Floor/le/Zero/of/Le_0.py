from util import *


@apply(simplify=None)
def apply(is_nonpositive):
    x = is_nonpositive.of(Expr <= 0)
    return LessEqual(Floor(x), 0)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    x = Symbol(real=True)
    Eq << apply(x <= 0)

    Eq << Set.Any_In_Ico.apply(x)

    Eq << Eq[-1].this.expr.apply(Set.Ge.Le.of.In_Icc)

    Eq << Bool.Any_And.of.Any.All.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[1:].apply(Algebra.Ge.of.Le.Ge, ret=1)

    Eq << Eq[-1].this.expr.args[::2].apply(Set.In.Icc.of.Lt.Ge)

    Eq << Eq[-1].this.expr.args[1].apply(Set.EqFloor.of.In)

    Eq << Eq[-1].this.expr.apply(Algebra.Ge.of.Ge.Eq)

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2019-12-06
# updated on 2023-05-18
