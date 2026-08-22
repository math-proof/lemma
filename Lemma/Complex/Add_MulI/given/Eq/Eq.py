from util import *


@apply
def apply(self):
    (x, y), (a, b) = self.of(Equal[Expr + ImaginaryUnit * Expr, Expr + ImaginaryUnit * Expr])
    return Equal(x, a), Equal(y, b)


@prove
def prove(Eq):
    x, y, a, b, c = Symbol(real=True, given=True)
    i = S.ImaginaryUnit
    Eq << apply(Equal(x + y * i, a + b * c * i))

    Eq << Eq[0].subs(Eq[1], Eq[2])


if __name__ == '__main__':
    run()
# created on 2018-06-03
