from util import *


@apply
def apply(A):
    from Lemma.Discrete.Alpha.gt.Zero import alpha
    x = A.of(alpha)
    n = x.shape[0] - 2

    assert n > 0
    x = x.base

    assert x.is_positive
    return Equal(A, alpha(x[:n], x[n] + 1 / x[n + 1]))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Logic
    from Lemma.Discrete.Alpha.gt.Zero import alpha

    x = Symbol(real=True, positive=True, shape=(oo,))
    n = Symbol(integer=True, positive=True, given=False)
    Eq << apply(alpha(x[:n + 2]))

    Eq.initial = Eq[-1].subs(n, 1)

    Eq << Eq.initial.this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Algebra.Cond.of.Cond.subst.apply(Eq[0], x[:n + 2], x[1:n + 3])

    Eq << Discrete.Alpha.ne.Zero.apply(x[1:n + 3])

    Eq << Algebra.EqInv.of.Ne_0.Eq.apply(Eq[-1], Eq[-2])

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Logic.Cond.of.Cond.All_Imp.apply(Eq.initial, Eq[-1], n=n, start=1)




if __name__ == '__main__':
    run()

# created on 2020-09-18
# updated on 2023-05-21
