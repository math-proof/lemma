from util import *



@apply
def apply(given):
    expr = given.of(Unequal[One])
    n, S[2] = expr.of(Mod)
    return Equal(expr, 0)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic
    n = Symbol(integer=True)

    Eq << apply(Unequal(n % 2, 1))

    Eq << Set.Mod.In.Range.apply(n % 2)

    Eq << Set.Or.of.In_Range.apply(Eq[-1])

    Eq << Logic.Cond.of.Or_Not.Cond.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-10-11
