from util import *


@apply
def apply(self):
    args, (old, new) = self.of(Subs[Add])
    return Equal(self, Add(*[Subs[old:new](arg) for arg in args]))


@prove
def prove(Eq):
    x, t = Symbol(real=True)
    f, g = Function(real=True)

    Eq << apply(Subs[x:t](f(x) + g(x)))

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[-1].this.rhs.args[0].doit()

    Eq << Eq[-1].this.rhs.doit()


if __name__ == '__main__':
    run()

# created on 2021-08-05
