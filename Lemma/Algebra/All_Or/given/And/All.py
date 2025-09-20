from util import *


@apply
def apply(given, index=-1):
    eqs, *limits = given.of(All[Or])

    first = And(*eqs[:index])
    second = And(*eqs[index:])
    return All(first, *limits), All(second, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a, b, c = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:a:b]((x <= c) | (f(x) >= 1)))



    Eq << Algebra.All_Or.given.All.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-02-06
