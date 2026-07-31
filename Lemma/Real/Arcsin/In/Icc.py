from util import *


@apply(simplify=False)
def apply(x):
    return Element(asin(x), Interval(-S.Pi / 2, S.Pi / 2))


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(x)

    

    


if __name__ == '__main__':
    run()
# created on 2023-10-03
