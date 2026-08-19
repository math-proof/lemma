from util import *


@apply
def apply(self, simplify=True):
    (expr, *l_limits), *s_limits = self.of(Integral[Stack])
    return Equal(self, Stack(Integral(expr, *s_limits), *l_limits), evaluate=False)


@prove(proved=False)
def prove(Eq):
    j = Symbol(integer=True)
    x = Symbol(real=True)
    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    Eq << apply(Integral[x](Stack[j:n](f[j](x))))

    

    


if __name__ == '__main__':
    run()
# created on 2023-04-02
