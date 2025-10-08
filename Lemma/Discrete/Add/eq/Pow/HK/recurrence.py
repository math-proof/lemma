from util import *


@apply
def apply(x):
    from Lemma.Discrete.H.eq.Add.definition import H
    from Lemma.Discrete.K.eq.Add.definition import K
    n = x.shape[0]
    n -= 1
    assert n > 0
    return Equal(H(x[:n + 1]) * K(x[:n]) - H(x[:n]) * K(x[:n + 1]), (-1) ** (n + 1))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    from Lemma.Discrete.H.eq.Add.definition import H
    from Lemma.Discrete.K.eq.Add.definition import K

    x = Symbol(integer=True, shape=(oo,))
    n = Symbol(integer=True, positive=True, given=False)

    Eq << apply(x[:n + 1])
    Eq.initial = Eq[-1].subs(n, 1)

    Eq << Eq.initial.this.find(H).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.find(Mul[-1, H, ~K]).defun()

    Eq << Eq[-1].this.find(~H * K).defun()

    Eq << Eq[-1].this.lhs.expand()

    Eq << -Eq[0]

    Eq << Eq[-1].this.rhs.expand()

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Bool.Cond.of.Cond.All_Imp.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()
# created on 2020-08-14
