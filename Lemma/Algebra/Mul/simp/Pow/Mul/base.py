from util import *


@apply
def apply(self, *, simplify=True):
    args = self.of(Mul)
    from Lemma.Algebra.Mul.eq.Pow.Mul.base import determine_args
    args, others = determine_args(args, simplify=simplify)
    args += others
    assert len(args) > 1
    return Equal(self, Mul(*args), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(real=True)
    t = Symbol(integer=True)
    Eq << apply(x ** t * y ** t * z * 2 ** x)

    Eq << Eq[-1].this.rhs.args[-1].apply(Algebra.Pow.eq.Mul.split.base)




if __name__ == '__main__':
    run()
# created on 2022-07-07
