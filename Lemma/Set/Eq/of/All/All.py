from util import *


@apply
def apply(all_A, all_B):
    A_function, (x, A) = all_A.of(All)
    S[A.image_set()[-1]], (S[x], B) = all_B.of(All)

    assert A_function == B.image_set()[-1]

    assert A.is_ConditionSet or A.definition.is_ConditionSet
    assert B.is_ConditionSet or B.definition.is_ConditionSet

    return Equal(A, B)


@prove
def prove(Eq):
    from Lemma import Set
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    f, g = Function(integer=True, shape=())
    A = Symbol(conditionset(x, Equal(f(x), 1)))
    B = Symbol(conditionset(x, Equal(g(x), 1)))

    assert f.is_integer and g.is_integer
    assert f.shape == g.shape == ()

    Eq << apply(All[x:A](Equal(g(x), 1)), All[x:B](Equal(f(x), 1)))
    Eq << Set.All_CupFinset.eq.Range.apply(A)

    Eq << Set.All_CupFinset.eq.Range.apply(B)

    Eq << All[x:A](Element(x, B), plausible=True)

    Eq << Eq[-1].this.expr.rhs.definition

    Eq << All[x:B](Element(x, A), plausible=True)

    Eq << Eq[-1].this.expr.rhs.definition

    Eq << Set.Eq.of.All_In.All_In.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-07-09
