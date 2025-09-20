from util import *


@apply
def apply(self):
    from Lemma.Algebra.Mul.eq.Pow.Add.exponent import determine_args
    ret, others = determine_args(self.of(Mul))
    assert others

    return Equal(self, ret * Mul(*others), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, t, z = Symbol(real=True)
    Eq << apply(t ** x * t * z)

    Eq << Eq[-1].this.find(Symbol ** Add).apply(Algebra.Pow.eq.Mul.split.exponent)




if __name__ == '__main__':
    run()
# created on 2022-07-07
# updated on 2023-05-14
