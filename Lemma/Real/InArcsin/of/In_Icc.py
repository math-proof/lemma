from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    assert b <= 1 and a >= -1
    return Element(asin(x), Interval(asin(a), asin(b)))


@prove(proved=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(0, 1)))


if __name__ == '__main__':
    run()
# created on 2018-06-25
