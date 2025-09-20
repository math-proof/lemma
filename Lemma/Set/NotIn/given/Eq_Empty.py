from util import *


@apply
def apply(given):
    n, s = given.of(NotElement)    
    return Equal(s, s.etype.emptySet)


@prove
def prove(Eq):
    x = Symbol(real=True, given=True)
    s = Symbol(etype=dtype.real)
    Eq << apply(NotElement(x, s))

    Eq << Eq[0].subs(Eq[1])
    


if __name__ == '__main__':
    run()
# created on 2022-01-28
