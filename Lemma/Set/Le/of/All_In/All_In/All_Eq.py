from util import *


@apply
def apply(all_a, all_b, equality_a):
    from Lemma.Set.Eq.of.All_In.All_In.All_Eq import analyze
    A, B, a, b, fa, gb = analyze(all_a, all_b, equality_a)
    return LessEqual(Card(A), Card(B))


@prove
def prove(Eq):
    from Lemma import Set
    m, n = Symbol(integer=True, positive=True)
    A = Symbol(etype=dtype.integer[n])
    a = Symbol(integer=True, shape=(n,))

    B = Symbol(etype=dtype.integer[m])
    b = Symbol(integer=True, shape=(m,))

    f = Function(integer=True, shape=(m,))
    g = Function(integer=True, shape=(n,))

    Eq << apply(All[a:A](Element(f(a), B)), All[b:B](Element(g(b), A)),
                All[a:A](Equal(a, g(f(a)))))

    Eq << Set.Eq.of.All_In.All_In.All_Eq.apply(Eq[0], Eq[1], Eq[2])

    Eq << Set.CardCup.le.Sum_Card.apply(*Eq[-1].lhs.args)

    Eq << Eq[-1].subs(Eq[-2])


if __name__ == '__main__':
    run()

# created on 2021-01-08
