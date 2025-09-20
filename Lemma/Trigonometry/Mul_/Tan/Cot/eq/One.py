from util import *


@apply
def apply(x):
    return Equal(cot(x) * tan(x), 1)


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << Eq[0].this.find(cot).apply(Trigonometry.Cot.eq.Inv.Tan)


if __name__ == '__main__':
    run()
# created on 2023-10-03
