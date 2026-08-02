from util import *


def H_step(x):
    if not x.shape:
        return x
    n, = x.shape
    if n == 2:
        return x[1] * x[0] + 1
    return Piecewise((x[0], Equal(n, 1)),
                     (x[1] * x[0] + 1, Equal(n, 2)),
                     (H(x[:n - 1]) * x[n - 1] + H(x[:n - 2]), True))


H = Function(integer=True, eval=H_step, shape=())


@apply
def apply(self):
    assert self.is_H
    x = self.arg
    n = x.shape[0]
    n -= 2
    assert n > 0
    return Equal(self, H(x[:n]) + H(x[:n + 1]) * x[n + 1])


@prove
def prove(Eq):
    x = Symbol(integer=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)

    Eq << apply(H(x[:n + 2]))

    Eq << Eq[-1].this.lhs.defun()


if __name__ == '__main__':
    run()
# created on 2021-07-30
