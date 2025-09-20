from util import *


@apply
def apply(self):
    assert self.is_extended_real
    return GreaterEqual(abs(self) - self, 0, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << Algebra.Le_Abs.apply(x).reversed - x










if __name__ == '__main__':
    run()
# created on 2019-09-15
