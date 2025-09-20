from util import *


@apply
def apply(all_a, all_b):
    from sympy.concrete.limits import limits_union
    fn, *limits_a = all_a.of(All)
    S[fn], *limits_b = all_b.of(All)
    limits = limits_union(limits_a, limits_b)
    return All(fn, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    e = Symbol(real=True)
    f, g = Function(integer=True)
    Eq << apply(All[e:g(e) > 0](f(e) > 0), All[e:g(e) < 0](f(e) > 0))

    Eq << Logic.All.All.of.All.apply(Eq[-1], cond=g(e) < 0)








if __name__ == '__main__':
    run()
# created on 2018-04-22
