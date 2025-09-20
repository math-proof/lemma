from util import *


@apply
def apply(self):
    f, *limits_d = self.of(Derivative)

    limits = []
    excludes = set()

    if f.shape:
        f_vars = []
        for m in f.shape:
            j = self.generate_var(excludes, integer=True)
            limits.append((j, 0, m))
            excludes.add(j)
            f_vars.append(j)

        f = f[tuple(f_vars)]

    wrts = []
    for x, n in limits_d:
        if not x.shape:
            wrts.append((x, n))
            continue

        for _ in range(n):
            x_vars = []
            for m in x.shape:
                j = self.generate_var(excludes, integer=True)
                limits.append((j, 0, m))
                x_vars.append(j)
                excludes.add(j)

            wrts.append((x[tuple(x_vars)], 1))

    limits.reverse()
    if wrts:
        rhs = Stack(Derivative(f, *wrts), *limits)
    else:
        rhs = Stack(f, *limits)

    return Equal(self, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n, m, d = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n, n))
    y = Symbol(real=True, shape=(m,))
    f = Function(real=True, shape=(d,))
    Eq << apply(Derivative[x, y ** 2](f(x, y)))

    i = Symbol(domain=Range(d))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)

    j = Symbol(domain=Range(n))
    k = Symbol(domain=Range(n))
    h = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], (j, k, h))

    t = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], t)



if __name__ == '__main__':
    run()
# created on 2021-12-25
del Mul
from . import Mul
