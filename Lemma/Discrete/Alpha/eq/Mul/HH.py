from util import *


def reverse(x):
    n = x.shape[0]
    i = x.generate_var(integer=True, free_symbols='i')
    return Stack[i:n](x[n - 1 - i])


@apply
def apply(x):
    from Lemma.Discrete.Alpha.gt.Zero import alpha
    from Lemma.Discrete.H.eq.Add.definition import H

    n = x.shape[0]
    assert x.is_positive
    assert n >= 2
    return Equal(alpha(reverse(x)), H(x[:n]) / H(x[:n - 1]))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Bool, Tensor
    from Lemma.Discrete.Alpha.gt.Zero import alpha
    from Lemma.Discrete.H.eq.Add.definition import H

    x = Symbol(real=True, positive=True, shape=(oo,))
#     x = Symbol(real=True, shape=(oo,))
    n = Symbol(domain=Range(2, oo), given=False)

    Eq << apply(x[:n])

    Eq.initial = Eq[0].subs(n, 2)

    Eq << Eq.initial.this.find(Stack).apply(Tensor.Stack.eq.Matrix)

    Eq << Eq[-1].this.lhs.apply(Discrete.Alpha.Matrix)

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Discrete.Alpha.ne.Zero.apply(reverse(x[:n]))

    Eq << Algebra.EqInv.of.Ne_0.Eq.apply(Eq[-1], Eq[0])

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Bool.Eq.of.Eq.All_Imp.apply(Eq.initial, Eq[-1], n=n, start=2)


if __name__ == '__main__':
    run()

# created on 2020-09-27
