from util import *


@apply
def apply(self, simplify=True):
    from Lemma.Algebra.Sum_Add.eq.AddSumS import associate
    return Equal(self, associate(Product, self, simplify=simplify))


@prove(provable=False)
def prove(Eq):
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    f, h = Function(real=True)
    Eq << apply(Product[i:n](f(i) * h(i)))


if __name__ == '__main__':
    run()

# created on 2018-04-14
