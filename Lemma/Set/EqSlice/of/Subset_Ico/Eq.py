from util import *


@apply
def apply(given, eq):
    (start, stop), (S[0], n) = given.of(Subset[Range, Range])
    a, b = eq.of(Equal)
    assert n <= a.shape[0]
    return Equal(a[start:stop], b[start:stop])

@prove(proved=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    a, b = Symbol(integer=True)
    x, y = Symbol(real=True, shape=(n,))
    Eq << apply(Subset(Range(a, b), Range(0, n)), Equal(x, y))

    


if __name__ == '__main__':
    run()
# created on 2022-01-04
