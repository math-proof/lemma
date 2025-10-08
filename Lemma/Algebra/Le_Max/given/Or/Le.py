from util import *


@apply
def apply(given, index=-1):
    x, args = given.of(Expr <= Max)
    first = args[:index]
    second = args[index:]

    return LessEqual(x, Max(*first)) | LessEqual(x, Max(*second))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x <= Max(y, z))
    Eq << ~Eq[0]
    Eq <<= Eq[-1] & Eq[1]
    Eq << Eq[-1].this.apply(Bool.OrAndS.of.And_Or)


if __name__ == '__main__':
    run()
# created on 2022-01-02
