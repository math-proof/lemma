from util import *



def K_step(x):
    if not x.shape:
        return S.One
    n, = x.shape
    if n == 2:
        return x[1]
    return Piecewise((1, Equal(n, 1)),
                     (x[1], Equal(n, 2)),
                     (K(x[:n - 1]) * x[n - 1] + K(x[:n - 2]), True))


K = Function(integer=True, eval=K_step, shape=())


@apply
def apply(self):
    assert self.is_K
    x = self.arg
    n = x.shape[0]
    n -= 2
    assert n > 0

    return Equal(self, K(x[:n]) + K(x[:n + 1]) * x[n + 1])


@prove
def prove(Eq):
    x = Symbol(integer=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)

    Eq << apply(K(x[:n + 2]))

    Eq << Eq[-1].this.lhs.defun()


if __name__ == '__main__':
    run()
# created on 2021-08-18
