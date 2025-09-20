from util import *


@apply
def apply(self):
    x = self.of(Max[0])

    return Equal(self, relu(x))


@prove
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(Max(0, x))

    Eq << Eq[-1].this.rhs.defun()



if __name__ == '__main__':
    run()
# created on 2021-12-19
