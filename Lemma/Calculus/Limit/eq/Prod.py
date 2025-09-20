from util import *


@apply
def apply(self, simplify=True):
    from Lemma.Calculus.Limit.eq.Sum import doit
    return Equal(self, doit(Product, self, simplify=simplify), evaluate=False)


@prove(proved=False)
def prove(Eq):
    k, n = Symbol(integer=True)
    s = Function(real=True)
    Eq << apply(Limit[n:oo](Product[k:n](s(k))))


if __name__ == '__main__':
    run()
# created on 2020-02-25
