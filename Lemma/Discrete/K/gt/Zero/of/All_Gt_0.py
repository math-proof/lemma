from util import *


@apply
def apply(given):
    from Lemma.Discrete.K.eq.Add.definition import K

    (x, j), (S[j], n) = given.of(All[Indexed > 0, Tuple[1, Expr]])
    return Greater(K(x[:n]), 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic, Set
    from Lemma.Discrete.K.eq.Add.definition import K
    x = Symbol(real=True, shape=(oo,))
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    Eq << apply(All[i:1:n](x[i] > 0))

    Eq.hypothesis = Imply(Eq[0], Eq[1], plausible=True)

    Eq.initial0 = Eq.hypothesis.subs(n, 1)

    Eq << Eq.initial0.this.lhs.defun()

    Eq.initial1 = Eq.hypothesis.subs(n, 2)

    Eq << Eq.initial1.this.find(K).defun()

    Eq.induct2 = Eq.hypothesis.subs(n, n + 2)

    Eq << Eq.induct2.this.find(K).defun()

    Eq.induct1 = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct1.this.lhs.apply(Set.AllIn.given.AllIn_Union, Range(1, n + 2))

    Eq << Logic.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-1].this.find(And, All).apply(Algebra.Cond.of.All.subst, Eq[-1].lhs.variable, n + 1)

    Eq << Eq[-1].this.find(And).apply(Algebra.Gt_0.of.Gt_0.Gt_0)

    Eq << Eq.hypothesis.this.lhs.apply(Set.AllIn.given.AllIn_Union, Range(1, n + 2))

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.find(And).apply(Algebra.Gt_0.Add.of.Gt_0.Gt_0)

    Eq << Imply(Eq.hypothesis & Eq.induct1, Eq.induct2, plausible=True)

    Eq << Logic.Cond.of.Cond.Cond.Imp.induct.apply(Eq.initial0, Eq.initial1, Eq[-1], n=n, start=1)

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq.hypothesis)
    Eq << Eq.hypothesis.subs(n, n + 1)
    Eq << Eq.hypothesis.subs(n, n + 2)





if __name__ == '__main__':
    run()

# created on 2020-09-15
# updated on 2023-05-21
