from util import *


@apply
def apply(self):
    args = self.of(Add)
    args = [arg.of(Abs ** 2) for arg in args]
    from Lemma.Algebra.Square.Abs.eq.Add.Re import sigmar2
    return Equal(self, Abs(Add(*args)) ** 2 - sigmar2(args))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(complex=True)
    Eq << apply(abs(x) ** 2 + abs(y) ** 2 + abs(z) ** 2)

    Eq << Eq[0].this.find(Abs[Add] ** 2).apply(Algebra.Square.Abs.eq.Add.Re)


if __name__ == '__main__':
    run()
# created on 2023-06-24
