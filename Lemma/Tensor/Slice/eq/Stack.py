from util import *


def convert(self, i=None):
    base, *indices = self.of(Sliced)
    if i is None:
        i = self.generate_var(integer=True)

    if len(indices) == 1:
        start, stop = self.index
        return Stack[i:stop - start](base[i + start])
    elif len(indices) == 2:
        for index in indices:
            start, stop = index
    else:
        return


@apply
def apply(self, i=None):
    rhs = convert(self, i)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a = Symbol(real=True, shape=(oo,))
    Eq << apply(a[:n])

    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], i)




if __name__ == '__main__':
    run()
# created on 2023-03-18
