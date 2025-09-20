from util import *


@apply
def apply(self):
    x = self.of(sin[Expr * Identity])
    return Equal(self, Identity(self.shape[-1]) * sin(x), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Trigonometry, Tensor

    x = Symbol(complex=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(sin(x * Identity(n)))

    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)

    j = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], j)

    Eq << Eq[-1].this.lhs.apply(Trigonometry.Sin.eq.Mul.Delta)




if __name__ == '__main__':
    run()
# created on 2023-06-08
