from util import *


@apply
def apply(self):
    fx, *limits = self.of(Expectation)
    if not fx.shape:
        fx = fx.of(Expr ** 2)
    elif fx.is_Mul:
        fx, S[fx] = fx.of(Expr * Transpose[Expr * Ones])
    else:
        fx, S[fx.T] = fx.of(MatMul)

    return Equal(self,
                 Expectation(fx, *limits).outer_product() + Variance(fx, *limits))

@prove
def prove(Eq):
    from Lemma import Probability

    n = Symbol(integer=True, positive=True)
    x = Symbol(integer=True, random=True, shape=(n,))
    Eq << apply(Expectation[x](x.outer_product()))

    Eq << Eq[-1].this.find(Variance).apply(Probability.Var.eq.Sub.Expect)




if __name__ == '__main__':
    run()
# created on 2023-03-24
# updated on 2023-04-14
