from util import *



def reverse(x):
    n = x.shape[0]
    i = x.generate_var(integer=True, free_symbols='i')
    return Stack[i:n](x[n - 1 - i])


@apply
def apply(x):
    from Lemma.Discrete.Alpha.gt.Zero import alpha
    from Lemma.Discrete.K.eq.Add.definition import K

    n = x.shape[0]
    assert x.is_positive
    n -= 1
    assert n >= 1
    return Equal(alpha(reverse(x[1:n + 1])), K(x[:n + 1]) / K(x[:n]))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Bool
    from Lemma.Discrete.K.eq.Add.definition import K
    from Lemma.Discrete.Alpha.gt.Zero import alpha

    x = Symbol(real=True, positive=True, shape=(oo,))
    n = Symbol(integer=True, positive=True, given=False)

    Eq << apply(x[:n + 1])

    Eq.initial = Eq[0].subs(n, 1)

    Eq << Eq.initial.this.find(alpha).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Discrete.Alpha.ne.Zero.apply(reverse(x[1:n + 1]))

    Eq << Algebra.EqInv.of.Ne_0.Eq.apply(Eq[-1], Eq[0])

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Bool.Eq.of.Eq.All_Imp.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

# created on 2020-09-27
