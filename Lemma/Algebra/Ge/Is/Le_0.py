from util import *


@apply
def apply(self):
    x, y = self.of(GreaterEqual)
    return LessEqual(y - x, Zeros(*x.shape))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x >= y)

    Eq << Eq[0].this.lhs.apply(Algebra.Ge.Is.Ge_0)

    Eq << -Eq[-1].this.lhs


if __name__ == '__main__':
    run()
# created on 2023-06-19
