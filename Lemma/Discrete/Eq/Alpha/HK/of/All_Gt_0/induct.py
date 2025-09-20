from util import *


@apply
def apply(given):
    from Lemma.Discrete.Alpha.gt.Zero import alpha
    from Lemma.Discrete.H.eq.Add.definition import H
    from Lemma.Discrete.K.eq.Add.definition import K
    (x, j), (S[j], n) = given.of(All[Indexed > 0, Tuple[1, Expr]])
    assert n >= 3
    assert x.is_real
    return Equal(alpha(x[:n]), H(x[:n]) / K(x[:n]))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Logic
    from Lemma.Discrete.Alpha.gt.Zero import alpha
    from Lemma.Discrete.H.eq.Add.definition import H
    from Lemma.Discrete.K.eq.Add.definition import K

    x = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    j = Symbol(integer=True)
    n = Symbol(domain=Range(2, oo), given=False)
    Eq << apply(All[j:1:n + 1](x[j] > 0))

    Eq.hypothesis = Imply(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 2)

    Eq << Eq.initial.this.lhs.doit()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt_0.of.Gt_0.Gt_0)

    Eq << Eq[-1].this.lhs + 1

    Eq << Eq[-1].this.lhs.apply(Algebra.Ne_0.of.Gt)

    Eq << Logic.Imp.given.Imp.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Ne_0.Eq.given.And.Mul)

    Eq << Eq[-1].this.rhs.lhs.ratsimp()

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq.alpha_recurrence = Eq.induct.lhs.this.apply(Discrete.EqAlpha.of.All_Gt_0.recurrence)

    # try to avoid using reciprocal expression, instead, using find(1 / Expr) to ensure logical correctness!
    Eq << Algebra.Cond.of.Cond.subst.apply(Eq.hypothesis, x[:n + 1], BlockMatrix(x[:n], Eq.alpha_recurrence.find(Indexed + 1 / Indexed)))

    Eq << Eq[-1].this.rhs.lhs.apply(Discrete.Alpha.Block)

    Eq << Eq[-1].this.lhs.apply(Algebra.All.given.And.All, cond={n})

    Eq << Eq[-1].this.find(All)().expr.simplify()

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Add.gt.Zero.given.And.Gt_0)

    Eq << Eq[-1].this.find(Greater[2]).apply(Algebra.Gt_0.given.Gt_0.Inv)

    Eq << Eq[-1].this.lhs.apply(Algebra.And.Is.All.limits.push)

    Eq <<= Eq.alpha_recurrence & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Logic.Eq.of.Eq.Eq, reverse=True)

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.rhs.rhs.ratsimp()

    Eq << Eq.induct.this.find(H).defun()

    Eq << Eq[-1].this.find(Indexed * ~H).defun()

    Eq << Eq[-1].this.find(Mul, Add).expand()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.find(Indexed * ~K).defun()

    Eq << Eq[-1].this.find(Pow, Add).expand()

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Logic.Cond.of.Cond.All_Imp.apply(Eq.initial, Eq[-1], n, 2)

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq.hypothesis)





if __name__ == '__main__':
    run()
# created on 2020-05-21
# updated on 2023-06-24
