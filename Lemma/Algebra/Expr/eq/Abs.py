from util import *


@apply
def apply(self):
    assert self >= 0
    return Equal(self, Abs(self, evaluate=False), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Int, Int

    x = Symbol(real=True, nonnegative=True)
    Eq << apply(x)

    Eq << Eq[0].this.rhs.apply(Int.Abs.eq.IteGe_0)




if __name__ == '__main__':
    run()
# created on 2023-04-03
