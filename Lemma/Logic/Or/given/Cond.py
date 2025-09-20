from util import *



@apply
def apply(imply, index=None):
    eqs = imply.of(Or)
    if index is None:
        return eqs
    return eqs[index]


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    x, y = Symbol(real=True, given=True)

    f = Function(real=True, given=True)

    Eq << apply((f(y) > 0) | (f(x) > 0), index=0)

    Eq << ~Eq[0]

    Eq << Logic.Cond.of.And.apply(Eq[-1], index=0)

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

# created on 2018-01-03
