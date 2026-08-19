from util import *


@apply
def apply(self):
    base, exponent = self.of(Pow)
    exponent = exponent.of(Add)

    args = [base ** e for e in exponent]

    return Equal(self, Mul(*args), evaluate=False)


@prove(provable=False)
def prove(Eq):
    x, b, a = Symbol(real=True, positive=True)



    Eq << apply(x ** (a + b))

if __name__ == '__main__':
    run()
# created on 2018-08-19
