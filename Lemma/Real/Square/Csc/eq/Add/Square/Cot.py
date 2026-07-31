from util import *


@apply
def apply(self):
    x = self.of(csc ** 2)
    return Equal(self, 1 + cot(x) ** 2)


@prove
def prove(Eq):
    from Lemma import Real

    x = Symbol(real=True)
    Eq << apply(csc(x) ** 2)

    Eq << Eq[0].this.find(cot ** 2).apply(Real.Square.Cot.eq.Sub.Square.Csc)


if __name__ == '__main__':
    run()
# created on 2023-11-26
