from util import *


@apply
def apply(self, simplify=True):
    from Lemma.Finset.Sum_Add.eq.AddSumS import associate
    return Equal(self, associate(Maxima, self, simplify=simplify))


@prove(provable=False)
def prove(Eq):
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    f, h = Function(real=True)
    Eq << apply(Maxima[i:n](Max(f(i), h(i))))


if __name__ == '__main__':
    run()
# created on 2023-04-23

from . import split
from . import pop
