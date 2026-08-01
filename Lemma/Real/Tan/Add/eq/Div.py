from util import *


@apply
def apply(self):
    x, y = self.of(tan[Add])
    return Equal(self, (tan(x) + tan(y)) / (1 - tan(x) * tan(y)))


@prove
def prove(Eq):
    from Lemma import Real

    x, y = Symbol(real=True)
    Eq << apply(tan(x + y))

    Eq << Eq[0].this.lhs.apply(Real.Tan.eq.Div)

    Eq << Eq[-1].this.find(tan).apply(Real.Tan.eq.Div)

    Eq << Eq[-1].this.find(tan).apply(Real.Tan.eq.Div)

    Eq << Eq[-1].this.find(tan).apply(Real.Tan.eq.Div)

    Eq << Eq[-1].this.find(tan).apply(Real.Tan.eq.Div)

    Eq << Eq[-1].this.rhs.ratsimp()

    Eq << Eq[-1].this.find(Sin[Add]).apply(Real.Sin.eq.Add)

    Eq << Eq[-1].this.find(Cos[Add]).apply(Real.CosAdd.eq.SubCosCos_SinSin)





if __name__ == '__main__':
    run()
# created on 2020-12-06
# updated on 2023-06-01
