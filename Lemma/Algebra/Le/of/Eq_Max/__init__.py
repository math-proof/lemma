from util import *


@apply
def apply(given, index=0):
    args, M = given.of(Equal[Max])
    return LessEqual(args[index], M)


@prove
def prove(Eq):
    from Lemma import Algebra

    M, x = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Equal(M, Max(f(x), g(x))))

    Eq << Algebra.Ge.of.Eq_Max.apply(Eq[0])
    Eq << Eq[-1].reversed



if __name__ == '__main__':
    run()
# created on 2023-04-23

from . import Eq_Min
