from util import *


@apply
def apply(given):
    from Lemma.Discrete.Alpha.gt.Zero import alpha

    (x, j), (S[j], n) = given.of(All[Indexed > 0, Tuple[1, Expr]])
    n = n - 2
    return Equal(alpha(x[:n + 2]), alpha(x[:n], x[n] + 1 / x[n + 1]))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Logic, Set
    from Lemma.Discrete.Alpha.gt.Zero import alpha

    x = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(All[i:1:n + 2](x[i] > 0))

    Eq.hypothesis = Imply(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 1)

    Eq << Eq.initial.this.lhs.doit()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct.this.find(alpha).defun()

    Eq << Eq[-1].this.rhs.rhs.defun()

    Eq << Algebra.Cond.of.Cond.subst.apply(Eq.hypothesis, x[:n + 2], x[1:n + 3])

    Eq << Eq[-1].this.lhs.apply(Algebra.All.limits.subst.offset, -1)

    Eq << Eq[-1].this.lhs.apply(Set.AllIn.given.AllIn_Union, Range(1, n + 3))

    Eq << Imply(All[i:1:n + 3](x[i] > 0), Unequal(alpha(x[1:n + 3]), 0), plausible=True)

    Eq << Eq[-1].this.lhs.apply(Discrete.Ne_0.Alpha.of.All_Gt_0.offset)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Algebra.EqInv.of.Ne_0.Eq)

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Logic.Cond.of.Cond.All_Imp.apply(Eq.initial, Eq[-1], n=n, start=1)

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq.hypothesis)





if __name__ == '__main__':
    run()

# created on 2020-09-24
# updated on 2023-11-12
