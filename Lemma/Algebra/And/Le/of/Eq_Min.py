from util import *


@apply
def apply(given, index=-1):
    args, M = given.of(Equal[Min])
    first = args[:index]
    second = args[index:]
    return LessEqual(M, Min(*first)), LessEqual(M, Min(*second))


@prove
def prove(Eq):
    from Lemma import Algebra

    M, x = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Equal(M, Min(f(x), g(x))))

    Eq << Algebra.Le.of.Eq_Min.apply(Eq[0], index=0)

    Eq << Algebra.Le.of.Eq_Min.apply(Eq[0], index=1)


if __name__ == '__main__':
    run()
# created on 2019-04-25
