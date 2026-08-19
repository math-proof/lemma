from util import *


@apply
def apply(self):
    print(__file__, 'is doubtable')
    expr, (x, x0) = self.of(Limit)
    args = expr.of(Add)

    return Equal(self, Add(*(Limit[x:x0](arg) for arg in args)))


@prove(proved=False)
def prove(Eq):
    x, x0 = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Limit[x:x0](f(x) + g(x)))

    A = Symbol(Eq[0].rhs.args[0])
    B = Symbol(Eq[0].rhs.args[1])
    Eq << A.this.definition

    Eq << B.this.definition


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function# Properties
# created on 2020-04-19
