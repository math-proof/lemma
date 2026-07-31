from util import *


@apply
def apply(contains):
    x, domain_x = contains.of(Element)
    assert domain_x in Interval(0, 1)
    return Element(acos(x), Interval(0, S.Pi / 2))


@prove(proved=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(0, 1)))


if __name__ == '__main__':
    run()
# created on 2021-09-05
