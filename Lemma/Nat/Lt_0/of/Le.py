from util import *



@apply
def apply(given):
    x, y = given.of(LessEqual)
    assert y < 0
    return Less(x, 0)


@prove
def prove(Eq):
    x = Symbol(real=True, given=True)
    y = Symbol(real=True, given=True, negative=True)
    Eq << apply(x <= y)

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2021-09-01
