from util import *


@apply
def apply(self):
    x, y = self.of(Arg[Expr + ImaginaryUnit * Expr])
    r = sqrt(x ** 2 + y ** 2)
    return Equal(self, Piecewise((0, Equal(x, 0) & Equal(y, 0)),
                                 (acos(x / r), y >= 0),
                                 (-acos(x / r), True)))


@prove(provable=False)
def prove(Eq):
    x, y = Symbol(real=True)
    Eq << apply(Arg(x + y * S.ImaginaryUnit))

    Eq << Eq[0].subs(x, 0)

    Eq << Eq[0].subs(y, 0)

    Eq << Eq[0].subs(x, 1).subs(y, 1)

    Eq << Eq[0].subs(x, -1).subs(y, 1)

    Eq << Eq[0].subs(x, -1).subs(y, -1)

    Eq << Eq[0].subs(x, 1).subs(y, -1)
    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2018-06-04
