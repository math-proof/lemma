from util import *


@apply
def apply(self):
    [*args], (variable, S[1]) = self.of(Difference[Add])
    rhs = Add(*(Difference(arg, (variable, 1)).simplify() for arg in args))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    f, g = Function(real=True)
    x = Symbol(real=True)
    Eq << apply(Difference[x](f(x) + g(x)))

    Eq << Eq[0].this.find(Difference).doit()

    Eq << Eq[-1].this.find(Difference).doit()
    Eq << Eq[-1].this.find(Difference).doit()




if __name__ == '__main__':
    run()
# created on 2020-10-08
