from util import *


@apply
def apply(self):
    from Lemma.Discrete.H.eq.Add.definition import H
    from Lemma.Discrete.K.eq.Add.definition import K
    assert self.is_alpha
    x = self.arg

    assert x.is_positive
    assert x.shape[0].is_finite

    return Equal(self, H(x) / K(x))


@prove
def prove(Eq):
    from Lemma import Logic
    from Lemma.Discrete.Alpha.gt.Zero import alpha
    from Lemma.Discrete.H.eq.Add.definition import H
    from Lemma.Discrete.K.eq.Add.definition import K

    from Lemma import Discrete, Algebra
    x = Symbol(real=True, positive=True, shape=(oo,))
    n = Symbol(integer=True)

    Eq.hypothesis = apply(alpha(x[:n + 1]))

    Eq.n2 = Imply(n >= 2, Eq.hypothesis, plausible=True)

    Eq << Eq.n2.this.apply(Logic.Imp.Is.All)

    _n = Symbol('n', domain=Range(2, oo))

    Eq << Discrete.Alpha.eq.Mul.HK.induct.apply(alpha(x[:_n + 1]))

    Eq << Logic.All.of.Cond.apply(Eq[-1], _n)

    Eq.n1 = Imply(Equal(n, 1), Eq.hypothesis, plausible=True)

    Eq << Eq.n1.this.apply(Logic.IffImpSAndEq)

    Eq << Eq[-1].this.rhs.subs(alpha(x[:2]).this.defun(),
                               alpha(x[1]).this.defun(),
                               H(x[:2]).this.defun(),
                               K(x[:2]).this.defun())

    Eq << Eq[-1].this.rhs.rhs.apart(x=x[1])

    Eq.n1 = Logic.ImpOrS.of.Imp.Imp.apply(Eq.n1, Eq.n2)

    Eq.n0 = Imply(Equal(n, 0), Eq.hypothesis, plausible=True)

    Eq << Eq.n0.this.apply(Logic.IffImpSAndEq)

    Eq << Eq[-1].this.rhs.subs(alpha(x[0]).this.defun(),
                               H(x[0]).this.defun(),
                               K(x[0]).this.defun())

    Eq << Logic.ImpOrS.of.Imp.Imp.apply(Eq.n1, Eq.n0)

    Eq << Eq[-1].this.apply(Logic.Imp.Is.All, wrt=n)

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

# created on 2020-09-20
