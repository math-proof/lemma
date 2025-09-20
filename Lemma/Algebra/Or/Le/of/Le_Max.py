from util import *


@apply
def apply(given, index=-1):
    x, args = given.of(Expr <= Max)
    first = args[:index]
    second = args[index:]

    return LessEqual(x, Max(*first)) | LessEqual(x, Max(*second))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x <= Max(y, z))

    Eq << Algebra.Or.Ge.of.Ge_Max.apply(Eq[0].reversed)

    Eq << Eq[-1].this.args[0].reversed

    Eq << Eq[-1].this.args[1].reversed


if __name__ == '__main__':
    run()
# created on 2022-01-02
