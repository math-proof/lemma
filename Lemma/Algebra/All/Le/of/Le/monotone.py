from util import *


@apply
def apply(le, n, N=None):
    an1, an = le.of(LessEqual)
    assert an._subs(n, n + 1) == an1
    if N is None:
        N = ge.generate_var(integer=True, var='N')
    return All[n:N:oo](an <= an._subs(n, N))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    a = Symbol(real=True, shape=(oo,), given=True)
    n, N = Symbol(integer=True)
    Eq << apply(a[n + 1] <= a[n], n, N)

    m = Symbol(integer=True, nonnegative=True, given=False)
    Eq << LessEqual(a[n + m], a[n], plausible=True)

    Eq.induct = Eq[-1].subs(m, m + 1)

    Eq << Eq[0].subs(n, m + n)

    Eq << Algebra.Le.of.Le.Le.apply(Eq[-1], Eq[-2])

    Eq << Imply(Eq[2], Eq.induct, plausible=True)

    Eq << Logic.Cond.of.All_Imp.apply(Eq[-1], n=m, start=0)

    Eq << Logic.All.of.Cond.apply(Eq[2], m)

    Eq << Eq[-1].subs(n, N)

    Eq << Eq[-1].limits_subs(Eq[-1].variable, n)

    Eq << Algebra.AllIn_Ico.of.AllIn_Ico.offset.apply(Eq[-1], -N)


if __name__ == '__main__':
    run()
# created on 2019-10-29
