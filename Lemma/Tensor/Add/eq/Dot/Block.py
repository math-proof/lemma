from util import *

def rewrite(self, swap=False):
    [*args] = self.of(Add)
    for i, A in enumerate(args):
        if A.is_MatMul:
            break
    else:
        return self

    del args[i]
    B = Add(*args)

    if B.is_Add:
        B = rewrite(B, swap=swap[1:])

    a, X = A.args
    if B.is_MatMul:
        b, Y = B.args
        if swap[0]:
            return S[b, a] @ [Y, X]
        else:
            return S[a, b] @ [X, Y]
    else:
        assert len(a.shape) == 1
        if swap[0]:
            return BlockMatrix(1, a) @ S[B, X].simplify()
        else:
            return BlockMatrix(a, 1) @ S[X, B].simplify()


@apply
def apply(self, swap=False):
    if isinstance(swap, bool):
        swap = (swap,) * len(self.args)
    return Equal(self, rewrite(self, swap=swap))

@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor

    t, k = Symbol(integer=True, positive=True)
    L = Symbol(shape=(oo, oo), super_complex=True)
    ξ = Symbol(r'{\color{red} {ξ}}', complex=True, shape=(oo,))
    Eq << apply(ξ[k + 1:t] @ L[k + 1:t, :k] + L[t, :k])

    Eq << Eq[0].this.rhs.args[1].apply(Algebra.Expr.eq.Block, t - k - 1)

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Block)





if __name__ == '__main__':
    run()
# created on 2023-06-27
# updated on 2023-09-18

