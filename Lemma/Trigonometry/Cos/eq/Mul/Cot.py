from util import *


@apply
def apply(self):
    x = self.of(cos)
    return Equal(self, cot(x) * sin(x))


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x = Symbol(real=True)
    Eq << apply(cos(x))

    Eq << Eq[0].this.find(cot).apply(Trigonometry.Cot.eq.Div)




if __name__ == '__main__':
    run()
# created on 2023-11-26
