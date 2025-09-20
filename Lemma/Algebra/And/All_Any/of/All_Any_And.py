from util import *


@apply
def apply(given, index=-1):
    (fn, *limits_e), *limits_f = given.of(All[Any])
    eqs, *limits = fn.of(All[And])

    first = And(*eqs[:index])
    second = And(*eqs[index:])


    return All(Any(All(first, *limits), *limits_e), *limits_f), All(Any(All(second, *limits), *limits_e), *limits_f)




@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z, a, b, c = Symbol(real=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(All[x:0:a](Any[y:0:b](All[z:0:c]((g(x, y, z) <= 1) & (f(x, y, z) >= 1)))))

    Eq << Algebra.All.Any.of.All_Any_And.apply(Eq[0], index=0)
    Eq << Algebra.All.Any.of.All_Any_And.apply(Eq[0], index=1)






if __name__ == '__main__':
    run()
# created on 2018-12-26
