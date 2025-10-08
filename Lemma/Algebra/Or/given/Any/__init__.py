from util import *


@apply
def apply(imply):
    from Lemma.Algebra.Any.of.Or import ou_to_any
    return ou_to_any(imply)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    x = Symbol(real=True)
    A, B = Symbol(etype=dtype.real, given=True)
    f = Function(integer=True)

    Eq << apply(boolalg.Or(Any[x:A]((f(x) > 0)), Any[x:B](f(x) > 0)))

    Eq << ~Eq[0]

    Eq << Eq[-1].apply(Bool.AllOr.of.All.All)

    Eq <<= Eq[1] & Eq[-1]


if __name__ == '__main__':
    run()

# created on 2020-02-17
del Or
from . import Or
