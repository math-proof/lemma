from util import *


@apply
def apply(el):
    x, domain = el.of(Element)
    assert domain in Interval.open(0, S.Pi)
    return sin(x) > x * (S.Pi ** 2 - x ** 2)/(S.Pi ** 2 + x ** 2)

@prove(proved=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(Element(x, Interval.open(0, S.Pi)))

    


if __name__ == '__main__':
    run()
# created on 2023-10-03
