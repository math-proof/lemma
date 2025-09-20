from util import *


@apply
def apply(self):
    x, m = self.of(Pow[Exp[ImaginaryUnit * Expr], Expr ** -1])
    assert m > 0 and x.is_real and m.is_integer
    return Equal(self, exp(S.ImaginaryUnit * Arg(exp(S.ImaginaryUnit * x)) / m))


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    m = Symbol(integer=True, positive=True)
    Eq << apply(exp(S.ImaginaryUnit * x) ** (1 / m))






if __name__ == '__main__':
    run()
# created on 2018-08-21
