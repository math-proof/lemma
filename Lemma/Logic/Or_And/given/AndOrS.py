from util import *


@apply
def apply(self, index=-1):
    [*args] = self.of(Or)
    for i, eq in enumerate(args):
        if isinstance(eq, And):
            del args[i]
            break

    this = Or(*args)
    args = eq.args
    first = And(*args[:index])
    second = And(*args[index:])

    return (first | this).simplify(), (second | this).simplify()


@prove
def prove(Eq):
    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, given=True)
    f, g = Function(shape=(k,), real=True)
    Eq << apply(Or(Unequal(x, y) & (y > 0), Equal(f(x), g(y))))

    Eq <<= Eq[1] & Eq[2]


if __name__ == '__main__':
    run()

# created on 2018-01-04
