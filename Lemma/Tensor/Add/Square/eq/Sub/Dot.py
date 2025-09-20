from util import *


@apply
def apply(self):
    args = self.of(Add)
    args = [arg.of(Norm ** 2) for arg in args]
    from Lemma.Tensor.Square.Norm.eq.Add.Dot import sigmar2
    return Equal(self, Norm(Add(*args)) ** 2 - sigmar2(args))


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    n = Symbol(integer=True, positive=True)
    x, y, z = Symbol(complex=True, shape=(n,))
    Eq << apply(Norm(x) ** 2 + Norm(y) ** 2 + Norm(z) ** 2)

    Eq << Eq[0].this.find(Norm[Add] ** 2).apply(Tensor.Square.Norm.eq.Add.Dot)




if __name__ == '__main__':
    run()
# created on 2023-06-24
