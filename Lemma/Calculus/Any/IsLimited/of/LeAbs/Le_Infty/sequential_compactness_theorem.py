from util import *


@apply
def apply(given, le, a=None):
    (x, n), M = given.of(Abs[Indexed] <= Expr)
    if a is None:
        a = given.generate_var(integer=True, shape=(oo,), var='a')

    S[n], (S[n], cond) = le.of(Card[Cup[FiniteSet]] < oo)
    ((S[x], m), S[x[n]]), (S[m], S[n + 1], S[oo]) = cond.of(All[Indexed <= Expr])

    return Any[a:All[n:1:oo](a[n - 1] < a[n])](Element(Limit[n:oo](x[a[n]]), Reals))


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(real=True, shape=(oo,))
    M = Symbol(real=True, positive=True)
    n, m = Symbol(integer=True)
    # n is a sequence "peak" if x[m] <= x[n] foreach m > n
    Eq << apply(Abs(x[n]) <= M, Card({n: All[m:n + 1:oo](x[m] <= x[n])}) < oo)

    Eq << GreaterEqual(Eq[1].lhs, 0, plausible=True)

    Eq << Set.In.Ico.of.Ge.Lt.apply(Eq[-1], Eq[1])

    Eq << Set.Eq.of.In.definition.apply(Eq[-1])

    Eq << Set.Any.Eq.of.Eq_Card.real.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2023-11-11
# updated on 2023-11-15
