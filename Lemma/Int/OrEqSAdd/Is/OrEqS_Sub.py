from util import *


@apply
def apply(self, offset):
    eqs = []
    for eq in self.of(Or):
        a, b = eq.of(Equal)
        eqs.append(Equal(a + offset, b + offset))
    return Or(*eqs)


@prove
def prove(Eq):
    x, a, b, c = Symbol(complex=True)
    Eq << apply(Or(Equal(x + a, b), Equal(x + a, c)), -a)

    Eq << Eq[-1].this.lhs.args[0] - a

    Eq << Eq[-1].this.lhs.args[1] - a

    


if __name__ == '__main__':
    run()
# created on 2018-11-28
# updated on 2023-05-20
