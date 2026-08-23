from util import *


@apply
def apply(self, factor):
    base = self.of(Basic ** -1)
    assert factor.is_nonzero

    return Equal(self, factor / (base * factor).expand())


@prove
def prove(Eq):
    b, d = Symbol(real=True, positive=True)
    Eq << apply(1 / (b + 1 / d), d)

    Eq << (d * (b + 1 / d)).this.expand()

    Eq << Eq[0].subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()
# created on 2020-09-17
