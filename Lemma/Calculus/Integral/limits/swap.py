from util import *


@apply
def apply(self, i=0, j=1):
    from Lemma.Algebra.Sum.limits.swap import rewrite
    return Equal(self, rewrite(Integral, self, i, j))


@prove(provable=False)
def prove(Eq):
    a, b, c, d = Symbol(real=True, positive=True)
    x, y = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Integral[x:a:b, y:c:d](f(x) * g(x, y)))




if __name__ == '__main__':
    run()
# created on 2023-03-20
# updated on 2023-07-02
