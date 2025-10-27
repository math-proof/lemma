from util import *


@apply
def apply(given):
    return given.domain_definition()


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    f = Function(complex=True, shape=())
    x = Symbol(complex=True, shape=(n,))
    Eq << apply(1 / f(x) > 0)

    


if __name__ == '__main__':
    run()
# created on 2023-04-05
