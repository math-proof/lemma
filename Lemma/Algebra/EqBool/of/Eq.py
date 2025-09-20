from util import *


@apply
def apply(given):
    x, y = given.of(Equal)

    assert x.shape
    return Equal(Bool(x), Bool(y))


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(n, n))
    Eq << apply(Equal(x, y))
    
    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2022-02-20
