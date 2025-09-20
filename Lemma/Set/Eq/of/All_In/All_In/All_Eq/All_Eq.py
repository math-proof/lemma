from util import *


@apply
def apply(all_a, all_b, equality_a, equality_b):
    from Lemma.Set.Eq.of.All_In.All_In.All_Eq import analyze
    A, B, a, b, fa, gb = analyze(all_a, all_b, equality_a)

    if equality_b.is_ForAll:
        assert equality_b.variable == b
        assert equality_b.limits == all_b.limits
        equality_b = equality_b.expr

    S[Lambda(a, fa)(gb)] = equality_b.of(Equal[b])

    return Equal(Card(A), Card(B))


@prove
def prove(Eq):
    from Lemma import Set
    n, m = Symbol(integer=True, positive=True)
    A = Symbol(etype=dtype.integer[n])
    a = Symbol(integer=True, shape=(n,))

    B = Symbol(etype=dtype.integer[m])
    b = Symbol(integer=True, shape=(m,))

    f = Function(integer=True, shape=(m,))
    g = Function(integer=True, shape=(n,))

    Eq << apply(All[a:A](Element(f(a), B)), All[b:B](Element(g(b), A)),
                All[a:A](Equal(a, g(f(a)))), All[b:B](Equal(b, f(g(b)))))

    Eq << Set.Eq.of.All_In.All_In.All_Eq.apply(Eq[0], Eq[1], Eq[2])

    Eq << Set.Eq.of.All_In.All_In.All_Eq.apply(Eq[1], Eq[0], Eq[3])

    Eq << Set.EqCard.of.Eq.Eq.apply(Eq[-1], Eq[-2]).reversed


if __name__ == '__main__':
    run()

# created on 2020-07-31
