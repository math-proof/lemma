from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    assert domain in Interval(S.Pi / 2, S.Pi, left_open=True)
    return Less(cos(x), 0)


@prove(proved=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(S.Pi / 2, S.Pi, left_open=True)))








if __name__ == '__main__':
    run()
# created on 2018-06-22
