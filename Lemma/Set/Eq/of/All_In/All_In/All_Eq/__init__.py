from util import *


@apply
def apply(all_a, all_b, equality_a):
    A, B, a, b, fa, gb = analyze(all_a, all_b, equality_a)

    return Equal(Cup[b:B](gb.set), A)


def analyze(*given):
    all_a, all_b, equality_a = given

    (fa, B), (a, A) = all_a.of(All[Element])
    (gb, S[A]), (b, S[B]) = all_b.of(All[Element])

    assert fa._has(a) and gb._has(b)

    eqs = Equal(a, Lambda(b, gb)(fa))
    if equality_a.is_ForAll:
        equality_a, S[(a, A)] = equality_a.of(All)

    assert {*equality_a.of(Equal)} == {*eqs.args}

    return A, B, a, b, fa, gb


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    n, m = Symbol(integer=True, positive=True)
    A = Symbol(etype=dtype.integer[n])
    a = Symbol(integer=True, shape=(n,))
    B = Symbol(etype=dtype.integer[m])
    b = Symbol(integer=True, shape=(m,))
    f = Function(integer=True, shape=(m,))
    g = Function(integer=True, shape=(n,))
    Eq << apply(All[a:A](Element(f(a), B)), All[b:B](Element(g(b), A)),
                All[a:A](Equal(a, g(f(a)))))

    Eq << Eq[1].this.expr.apply(Set.SubsetSingleton.of.In, simplify=False)

    Eq.subset_A = Set.SubsetCup.of.All_Subset.apply(Eq[-1])

    Eq.supset_A = Eq.subset_A.func.reversed_type(*Eq.subset_A.args, plausible=True)

    Eq << Set.Supset.given.All_In.apply(Eq.supset_A, var=Eq[0].variable)

    Eq << Eq[-1].this.expr.apply(Set.In.given.Any.Eq.split.Imageset)

    Eq <<= Eq[-1] & Eq[2]

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Ufn.given.Eq.Ufn)

    Eq << Logic.All_And.given.All.All.apply(Eq[-1])

    Eq << All[a:A](Any[b:B](Equal(f(a), b)), plausible=True)

    Eq << Eq[-1].this.expr.simplify()

    Eq << Eq[-1].this.expr.expr.apply(Logic.EqUFnS.of.Eq, g)

    Eq <<= Eq.supset_A & Eq.subset_A




if __name__ == '__main__':
    run()

# created on 2020-07-30
# updated on 2023-08-26

from . import All_Eq
