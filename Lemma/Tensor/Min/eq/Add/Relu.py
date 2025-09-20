from util import *


@apply
def apply(self, index=-1):
    [*args] = self.of(Min)

    y = args.pop(index)
    x = Min(*args)

    return Equal(self, y - relu(-x + y))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True)
    Eq << apply(Min(x, y))

    Eq << Eq[0].this.rhs.args[1].args[1].defun()

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Mul.eq.Min)

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Min)





if __name__ == '__main__':
    run()
# created on 2020-12-29
# updated on 2021-12-18