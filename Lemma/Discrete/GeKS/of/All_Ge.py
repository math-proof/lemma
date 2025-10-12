from util import *


@apply
def apply(given):
    from Lemma.Discrete.K.eq.Add.definition import K

    (x, j), (S[j], n1) = given.of(All[Indexed >= 1, Tuple[1, Expr]])

    n = n1 - 1

    return GreaterEqual(K(x[:n + 1]), K(x[:n]))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Bool, Nat
    from Lemma.Discrete.K.eq.Add.definition import K
    x = Symbol(real=True, shape=(oo,))
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    Eq << apply(All[i:1:n + 1](x[i] >= 1))

    Eq.case2, Eq.case1 = Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=n >= 2)

    Eq << Eq.case1.this.lhs.apply(Algebra.Lt.Is.Eq.squeeze)

    Eq << Eq[-1].this.apply(Bool.IffImpSAndEq)

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Bool.Imp.given.Cond.apply(Eq[-1])

    Eq << Algebra.Cond.of.All.subst.apply(Eq[0], i, 1)

    _n = Symbol('n', domain=Range(2, oo))

    Eq << Eq[0].subs(n, _n)

    Eq << Discrete.GtKS.of.All_Ge.apply(Eq[-1])

    Eq << Bool.All.of.Cond.apply(Eq[-1], _n)

    Eq << Eq[-1].this.expr.apply(Nat.Ge.of.Gt)

    Eq << Bool.Imp.given.All.apply(Eq.case2)


if __name__ == '__main__':
    run()

# created on 2020-09-16
