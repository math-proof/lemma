from util import *


@apply
def apply(self):
    x = self.of(Arg[Exp[ImaginaryUnit * Expr]])
    return Equal(self, x - Ceil(x / (S.Pi * 2) - S.One / 2) * S.Pi * 2)


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(Arg(exp(S.ImaginaryUnit * x)))

    Eq << Eq[-1].subs(x, S.Pi / 2)

    Eq << Eq[-1].subs(x, S.Pi / 3)

    Eq << Eq[-1].subs(x, S.Pi / 4)

    Eq << Eq[-1].subs(x, 0)

    Eq << Eq[-1].subs(x, -S.Pi / 4)

    Eq << Eq[-1].subs(x, -S.Pi / 3)

    Eq << Eq[-1].subs(x, -S.Pi / 2)

    Eq << Eq[-1].subs(x, -S.Pi)


if __name__ == '__main__':
    run()
# created on 2018-08-25
