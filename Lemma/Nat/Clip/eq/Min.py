from util import *


@apply
def apply(self):
    x, a, b = self.of(clip)
    return Equal(self, Min(Max(x, a), b))


@prove
def prove(Eq):
    x, a, b = Symbol(real=True)
    Eq << apply(clip(x, a, b))

    Eq << Eq[-1].this.lhs.defun()


if __name__ == '__main__':
    run()
# created on 2023-03-26
