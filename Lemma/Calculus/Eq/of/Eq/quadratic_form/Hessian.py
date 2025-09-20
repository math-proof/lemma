from util import *


@apply
def apply(eq):
    (c, b_x, A_x2), f = eq.of(Equal[Add])
    assert f.is_Function
    x = f.arg
    b, S[x] = b_x.of(MatMul)
    S[x], A, S[x] = A_x2.of(MatMul)
    return Equal(Derivative(f, (x, 2)), A + A.T)


@prove
def prove(Eq):
    from Lemma import Calculus

    n = Symbol(integer=True, positive=True)
    x = Symbol(r"\vec x", real=True, shape=(n,))
    f = Function(real=True, shape=())
    c = Symbol(real=True)
    b = Symbol(r"\vec b", real=True, shape=(n,))
    A = Symbol(r"\boldsymbol A", real=True, shape=(n, n))
    Eq << apply(Equal(f(x), c + b @ x + x @ A @ x))

    Eq << Calculus.EqGrad.of.Eq.apply(Eq[0], (x,))

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.eq.Add)

    Eq << Eq[-1].this.rhs.args[0].apply(Calculus.Grad_Add_Dot.simp)

    Eq << Eq[-1].this.rhs.args[1].apply(Calculus.Grad_DotDot.eq.DotAdd)

    Eq << Calculus.EqGrad.of.Eq.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.eq.Add)

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad_Add_Dot.simp)





if __name__ == '__main__':
    run()
# created on 2021-12-25
# updated on 2022-01-01