from util import *


@apply
def apply(x, negate=False):
    if negate:
        x = -x
    return LessEqual(x, abs(x))


@prove
def prove(Eq):
    from Lemma import Algebra, Int, Nat

    x = Symbol(real=True, given=True)
    Eq << apply(x)

    Eq << ~Eq[-1]

    Eq << GreaterEqual(abs(x), 0, plausible=True)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.apply(Nat.Gt.of.Gt.Ge, ret=0, simplify=None)

    Eq << Eq[-1].this.args[0].apply(Int.EqAbs.of.Gt_0, simplify=None)

    Eq << Eq[-1].this.apply(Nat.Gt.of.Gt.Eq)



if __name__ == '__main__':
    run()

# created on 2018-06-29
# updated on 2022-01-04

del given
from . import given
