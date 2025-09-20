from util import *


@apply
def apply(ne_zero, self):
    AT, A = std.array_split(ne_zero.of(Unequal[Det[Add], 0]), lambda arg: arg.is_Transpose)

    A = Add(*A)
    if AT:
        AT = Add(*AT)
    else:
        AT = A.T
    assert AT == A.T

    [*terms] = self.of(Add)

    AI = A.inverse()
    # find quadratic term
    for i, term in enumerate(terms):
        if term.is_MatMul:
            args = term.args
            if args[0] == args[-1]:
                x = args[0]
                prod = MatMul(*args[1:-1])
                if prod == AI:
                    A, AI = AI, A
                    break

                if A == prod:
                    break
    else:
        return

    del terms[i]
    # find simple term
    for i, term in enumerate(terms):
        if term.is_MatMul:
            args = term.args
            coeff = 1
        elif term.is_Mul:
            coeff, args = term.of(Expr * MatMul)
        else:
            args = None

        if args:
            if args[0] == x:
                b = MatMul(*args[1:]) * coeff
                break

            if args[-1] == x:
                b = MatMul(*args[:-1]) * coeff
                break
    else:
        return

    del terms[i]

    c = Add(*terms)

    if A == A.T:
        h = (A ^ -1) @ b / 2
    else:
        h = ((A + A.T) ^ -1) @ b
    k = c - h @ A @ h
    return Equal(self, (x + h) @ A @ (x + h) + k)


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    n = Symbol(integer=True, positive=True)
    x = Symbol(r"\vec x", real=True, shape=(n,))
    c = Symbol(real=True)
    b = Symbol(r"\vec b", real=True, shape=(n,))
    A = Symbol(r"\boldsymbol A", real=True, shape=(n, n))
    Eq << apply(Unequal(Det(A + A.T), 0),  c + b @ x + x @ A @ x)

    Eq << Eq[1].this.find(MatMul[Add]).apply(Tensor.Dot.eq.Add)

    Eq << Eq[-1].this.find(MatMul[Add]).apply(Tensor.Dot.eq.Add)

    Eq << Eq[-1].this.find(MatMul[Add]).apply(Tensor.Dot.eq.Add)

    Eq << Eq[-1].this.rhs.args[0].T

    Eq << Eq[-1].this.rhs.apply(Tensor.Add.eq.Dot)

    Eq << Eq[-1].this.find(Add).apply(Tensor.Add.eq.Dot)

    # https://en.wikipedia.org/wiki/Completing_the_square# Matrix_case



if __name__ == '__main__':
    run()
# created on 2023-04-30
# updated on 2023-05-19
