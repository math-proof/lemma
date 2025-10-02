from util import *


@apply
def apply(self):
    x = self.of(Log[ReducedSum[Exp]])

    return Equal(self, logsumexp(x))


@prove
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(Log(ReducedSum(Exp(x))))


    Eq << Eq[0].this.rhs.defun()


if __name__ == '__main__':
    run()
# created on 2021-12-19
