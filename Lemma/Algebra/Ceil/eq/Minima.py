from util import *


@apply
def apply(self):
    x = self.of(Ceil)
    n = x.generate_var(integer=True, var='n')
    return Equal(self, Minima[n:n>=x](n))


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(Ceil(x))

    # Eq << Eq[0].reversed + 1 - Floor(x)
    # Eq << Eq[-1].this.lhs.apply(Algebra.add.to.frac)


if __name__ == '__main__':
    run()

# created on 2021-09-11
