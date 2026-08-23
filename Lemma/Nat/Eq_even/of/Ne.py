from util import *



@apply
def apply(given):
    expr = given.of(Unequal[One])
    n, S[2] = expr.of(Mod)
    return Equal(expr, 0)


@prove
def prove(Eq):
    from Lemma import Set, Bool
    n = Symbol(integer=True)

    Eq << apply(Unequal(n % 2, 1))

    Eq << Set.Mod.In.Range.of.Gt_0.apply(n % 2)

    Eq << Set.Or_Eq.of.In_Ico.apply(Eq[-1])

    Eq << Bool.Cond.of.Or_Not.Cond.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-10-11
