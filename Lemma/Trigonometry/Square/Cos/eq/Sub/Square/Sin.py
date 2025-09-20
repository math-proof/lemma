from util import *


@apply
def apply(self):
    x = self.of(Cos ** 2)
    return Equal(self, 1 - sin(x) ** 2)


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x = Symbol(real=True)
    Eq << apply(cos(x) ** 2)

    Eq << Eq[0].this.find(sin ** 2).apply(Trigonometry.Square.Sin.eq.Sub.Square.Cos)






if __name__ == '__main__':
    run()
# created on 2023-06-21
# updated on 2023-11-26
