from util import *


@apply
def apply(given, index=-1):
    args = given.of(Add > 0)
    first = args[:index]
    first = Add(*first)
    second = args[index:]
    second = Add(*second)
    return first > 0, second > 0


@prove
def prove(Eq):
    from Lemma import Algebra

    a, b = Symbol(real=True, given=True)
    Eq << apply(a + b > 0)

    Eq << Algebra.Gt_0.Add.of.Gt_0.Gt_0.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()
# created on 2018-08-12
