from util import *


@apply
def apply(given, index=-1):
    x, args = given.of(Expr >= Max)
    if index is None:
        eqs = [x >= arg for arg in args]
    else:
        first = args[:index]
        second = args[index:]
        eqs = x >= Max(*first), x >= Max(*second)

    return And(*eqs)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x >= Max(y, z))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.And.Ge.of.Ge_Max)

    Eq << Eq[-1].this.lhs.apply(Algebra.GeMax.of.Ge.Ge)




if __name__ == '__main__':
    run()
# created on 2022-01-01
