from util import *


@apply
def apply(ne_zero_A, ne_zero_B, ne_zero, self):
    A, S[A] = ne_zero_A.of(Unequal[Det[Expr + Transpose], 0])
    B, S[B] = ne_zero_B.of(Unequal[Det[Expr + Transpose], 0])
    S[A], S[B], S[A], S[B] = ne_zero.of(Unequal[Det[Expr + Expr + Transpose + Transpose], 0])
    ((x, y), A, S[x - y]), ((S[x], z), B, S[x - z]) = self.of((Expr - Expr) @ Expr @ Expr + (Expr - Expr) @ Expr @ Expr)

    h = ((A + B + A.T + B.T) ^ -1) @ ((A + A.T) @ y + (B + B.T) @ z)
    k = (y - z) @ ((((A + A.T) ^ -1) + ((B + B.T) ^ -1)) ^ -1) @ (y - z) / 2
    return Equal(self, (x - h) @ (A + B) @ (x - h) + k)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor, Bool

    n = Symbol(integer=True, positive=True)
    x = Symbol(r"\vec x", real=True, shape=(n,))
    y = Symbol(r"\vec y", real=True, shape=(n,))
    z = Symbol(r"\vec z", real=True, shape=(n,))
    A = Symbol(r"\boldsymbol A", real=True, shape=(n, n))
    B = Symbol(r"\boldsymbol B", real=True, shape=(n, n))
    Eq << apply(Unequal(Det(A + A.T), 0), Unequal(Det(B + B.T), 0), Unequal(Det(A + A.T + B + B.T), 0), (x - y) @ A @ (x - y) + (x - z) @ B @ (x - z))

    P = Symbol(Eq[-1].lhs)
    Eq << P.this.definition

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Add)

    Eq << Eq[-1].this.rhs.find(MatMul[Add]).apply(Tensor.Dot.eq.Add, simplify=None)

    Eq << Eq[-1].this.rhs.find(MatMul[Add]).apply(Tensor.Dot.eq.Add)

    Eq << Eq[-1].this.rhs.find(MatMul[Add]).apply(Tensor.Dot.eq.Add)

    Eq << Eq[-1].this.rhs.find(MatMul[Add]).apply(Tensor.Dot.eq.Add)

    Eq << Eq[-1].this.rhs.find(MatMul[Add]).apply(Tensor.Dot.eq.Add)

    Eq << Eq[-1].this.rhs.args[:2].apply(Tensor.Add.eq.Dot)

    Eq << Eq[-1].this.rhs.args[-3].T

    Eq << Eq[-1].this.rhs.args[3].T

    Eq << Eq[-1].this.rhs.args[3:5].apply(Tensor.Add.eq.Dot)

    Eq << Eq[-1].this.rhs.find(MatMul[Add[-Expr, -Expr]]).apply(Tensor.Dot.eq.Neg)

    Eq << Eq[-1].this.rhs.args[-2:].apply(Tensor.Add.eq.Dot)

    Eq << Eq[-1].this.rhs.find(MatMul[Add[-Expr, -Expr]]).apply(Tensor.Dot.eq.Neg)

    Eq << Eq[-1].this.rhs.args[-2:].apply(Tensor.Add.eq.Dot)

    Eq << Eq[-1].this.rhs.find(MatMul[Add[-Expr, -Expr]]).apply(Tensor.Dot.eq.Neg)

    Eq << Discrete.Eq.of.Ne_0.square_completing.apply(Eq[2], Eq[-1].rhs)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(MatMul[Add[-MatMul, -MatMul]]).apply(Tensor.Dot.eq.Neg)

    Eq << Eq[-1].this.find(MatMul[Add[-MatMul, -MatMul]]).apply(Tensor.Dot.eq.Neg)

    Eq << Eq[-1].rhs.args[2].find(Add[MatMul[Add]]).this.args[0].T

    Eq << Eq[-1].this.rhs.args[0].T

    Eq << Eq[-3].subs(Eq[-1])

    Eq.eq = Algebra.Eq.of.Eq.transport.apply(Eq[-1], rhs=2)

    W = Symbol(Eq.eq.rhs)
    Eq << W.this.definition

    Eq << Eq[-1].this.find(MatMul[Add[-MatMul, -MatMul]]).apply(Tensor.Dot.eq.Neg)

    Eq << Eq[-1].this.find(MatMul[Add[-MatMul, -MatMul]]).apply(Tensor.Dot.eq.Neg, 4)

    Eq << Eq[-1].this.find(MatMul[Add]).apply(Tensor.Dot.eq.Add)

    Eq << Eq[-1].this.find(MatMul[Add]).apply(Tensor.Dot.eq.Add, 5)

    Eq << Eq[-1].this.find(MatMul[Add]).apply(Tensor.Dot.eq.Add, 5)

    # combine y square terms
    Eq << Eq[-1].this.rhs.args[0:4:2].apply(Tensor.Add.eq.Dot)

    # combine z square terms
    Eq << Eq[-1].this.rhs.args[::4].apply(Tensor.Add.eq.Dot)

    Eq << Eq[-1].this.rhs.args[-1].T

    Eq << Eq[-1].this.rhs.args[-2:].apply(Tensor.Add.eq.Dot)

    Eq << Eq[-1].this.rhs.args[-1].apply(Tensor.Dot.eq.Neg, 3)

    Eq << Eq[-1].T

    Eq << Eq[-1].this.rhs.args[-1].T

    Eq << Eq[-1] + Eq[-3]

    Eq << Eq[-1].this.rhs.args[:2].apply(Tensor.Add.eq.Dot)

    Eq << Eq[-1].this.rhs.args[1:3].apply(Tensor.Add.eq.Dot)

    Eq << Eq[-1].this.rhs.args[0].args[1].args[1:3:].apply(Tensor.Add.eq.Dot)

    Eq << Eq[-1].this.rhs.args[0].args[1].args[1].apply(Tensor.Dot.eq.Mul, 2)

    Eq << Eq[-1].this.rhs.args[1].args[1].args[1:3:].apply(Tensor.Add.eq.Dot)

    Eq << Eq[-1].this.rhs.args[1].args[1].args[1].apply(Tensor.Dot.eq.Mul, 2)

    Eq << Eq[-1].this.rhs.args[0].args[1].args[1].args[1].args[-2:].apply(Tensor.Dot.eq.Sub)

    Eq << Eq[-1].this.rhs.args[0].find(MatMul[Add]).apply(Tensor.Dot.eq.Add, 1)

    Eq << Eq[-1].this.rhs.args[0].args[1].args[1].args[1].args[-2:].apply(Tensor.Dot.eq.Sub)

    Eq << Eq[-1].this.rhs.args[0].find(MatMul[Add]).apply(Tensor.Dot.eq.Add, 1)

    Eq << Eq[-1].this.rhs.args[1].T

    Eq << Discrete.EqInv.of.Ne_0.Ne_0.Ne_0.apply(*Eq[:3])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Algebra.Ne_0.of.Div1.gt.Zero.apply(Eq[-1])

    Eq << Discrete.Eq.of.Ne_0.square_completing.apply(Eq[-1], Eq[-2].rhs)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1] / 2

    Eq << Eq.eq.subs(W.this.definition.reversed)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Eq.of.Eq.transport.apply(Eq[-1], lhs=-1)

    Eq << Eq[-1].this.lhs.definition

    # https://en.wikipedia.org/wiki/Normal_distribution# Vector_form




if __name__ == '__main__':
    run()
# created on 2023-04-30
# updated on 2023-05-19
