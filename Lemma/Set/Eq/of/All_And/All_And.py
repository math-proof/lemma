from util import *


@apply
def apply(all_a, all_b):
    (contains_a, equality_a), (a, A) = all_a.of(All[And])
    (contains_b, equality_b), (b, B) = all_b.of(All[And])

    if contains_a.is_Equal:
        equality_a, contains_a = contains_a, equality_a

    if contains_b.is_Equal:
        equality_b, contains_b = contains_b, equality_b

    fa, S[B] = contains_a.of(Element)
    gb, S[A] = contains_b.of(Element)

    S[Lambda(b, gb)(fa)] = equality_a.of(Equal[a])

    S[Lambda(a, fa)(gb)] = equality_b.of(Equal[b])

    return Equal(Card(A), Card(B))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    n, m = Symbol(integer=True, positive=True)

    A = Symbol(etype=dtype.integer[n])
    a = Symbol(integer=True, shape=(n,))

    B = Symbol(etype=dtype.integer[m])
    b = Symbol(integer=True, shape=(m,))

    f = Function(integer=True, shape=(m,))
    g = Function(integer=True, shape=(n,))

    Eq << apply(All[a:A](Element(f(a), B) & Equal(a, g(f(a)))),
                All[b:B](Element(g(b), A) & Equal(b, f(g(b)))))

    Eq << Logic.All.All.of.All_And.apply(Eq[0])

    Eq << Logic.All.All.of.All_And.apply(Eq[1])

    Eq << Set.Eq.of.All_In.All_In.All_Eq.All_Eq.apply(Eq[-3], Eq[-1], Eq[-4], Eq[-2])


if __name__ == '__main__':
    run()

# created on 2020-08-01
