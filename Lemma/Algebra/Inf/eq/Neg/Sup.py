from util import *


@apply
def apply(self):
    function, *limits = self.of(Inf)

    return Equal(self, -Sup(-function, *limits), evaluate=False)


@prove
def prove(Eq):
    x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:a:b](f(x)))

    Eq << Eq[-1].this.find(Sup).simplify()





if __name__ == '__main__':
    run()
# created on 2021-09-30
