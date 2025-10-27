from util import *


@apply
def apply(x, k=None):
    from Lemma.Discrete.Sigma.eq.Add.recurrent import sigma
    n = x.shape[0]
    if k is None:
        k = Symbol(integer=True)

    return All[k:1:n](GreaterEqual((sigma[k](x[:n]) / binomial(n, k)) ** (1 / k),
                                      (sigma[k + 1](x[:n]) / binomial(n, k + 1)) ** (1 / (k + 1))))




@prove(proved=False)
def prove(Eq):
    from Lemma import Algebra, Nat
    from Lemma.Discrete.Sigma.eq.Add.recurrent import sigma
    n = Symbol(domain=Range(2, oo), given=False)
    x = Symbol(real=True, positive=True, shape=(oo,))
    k = Symbol(integer=True)
    Eq << apply(x[:n], k)

    Eq.initial = Eq[0].subs(n, 2)

    Eq << Eq.initial.this.find(sigma).defun()

    Eq << Eq[-1].this.find(sigma).defun()

    Eq << Eq[-1].this.find(Product).apply(Algebra.Prod.eq.Mul.doit)

    Eq << Eq[-1].this.find(All).apply(Algebra.All.Is.And.doit.outer)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Add.doit)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.shift.CartesianSpace.Cond)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Add.doit.outer)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.delete.Condset)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.delete.Condset)

    Eq << Eq[-1].this.find(Sum).simplify()

    Eq << Eq[-1] * 2

    Eq << Algebra.Add_.AddSquareS.Mul2.ge.Zero.apply(sqrt(x[0]) - sqrt(x[1]))

    Eq << Algebra.Ge.of.Ge_0.apply(Eq[-1])

    t = Function(real=True, eval=lambda k: (sigma[k](x[:n]) / binomial(n, k)) ** (1 / k))
    k_ = Symbol("k", domain=Range(2, n))
    Eq << t(k_).this.defun()

    Eq << Nat.EqPowS.of.Eq.apply(Eq[-1], exp=k_)

    Eq << Eq[-1] * binomial(n, k_)

    Eq.s_k = Eq[-1].reversed

    Eq << t(k_ + 1).this.defun()

    Eq << Nat.EqPowS.of.Eq.apply(Eq[-1], exp=k_ + 1)

    Eq << Eq[-1] * binomial(n, k_ + 1)

    Eq.s_k1 = Eq[-1].reversed

    Eq << t(k_ - 1).this.defun()

    Eq << Nat.EqPowS.of.Eq.apply(Eq[-1], exp=k_ - 1)

    Eq << Eq[-1] * binomial(n, k_ - 1)

    Eq.s_k1_neg = Eq[-1].reversed

    Eq << Algebra.Cond.of.All.subst.apply(Eq[0], k, k_)

    Eq.hypothesis_k = Eq[-1].subs(t(k_).this.defun().reversed).subs(t(k_ + 1).this.defun().reversed)

    Eq << Algebra.Cond.of.All.subst.apply(Eq[0], k, k_ - 1)

    Eq.hypothesis_k_1 = Eq[-1].subs(t(k_).this.defun().reversed).subs(t(k_ - 1).this.defun().reversed)

    Eq << Eq[0].subs(n, n + 1)

    Eq << GreaterEqual(((sigma[k_](x[:n]) + x[n] * sigma[k_ - 1](x[:n])) / binomial(n, k_)) ** (1 / k_),
                       ((sigma[k_ + 1](x[:n]) + x[n] * sigma[k_](x[:n])) / binomial(n, k_ + 1)) ** (1 / (k_ + 1)), plausible=True)

    return
    Eq << Eq[-1].subs(Eq.s_k)
    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.to.add)
    Eq << Eq[-1].subs(Eq.s_k1)
    Eq << Eq[-1].this.rhs.find(Mul).apply(Algebra.Mul.to.add)
    Eq << Eq[-1].subs(Eq.s_k1_neg)



if __name__ == '__main__':
    run()

# created on 2020-11-05
# updated on 2023-08-20
