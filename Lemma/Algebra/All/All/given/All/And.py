from util import *


@apply
def apply(all_a, all_b):
    fn, *limits = all_a.of(All)
    _fn, *S[limits] = all_b.of(All)
    return All(fn & _fn, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    e = Symbol(real=True)
    f, g, h = Function(integer=True)
    Eq << apply(All[e:g(e) > 0](f(e) > 0), All[e:g(e) > 0](h(e) > 0))

    Eq << Logic.All.All.of.All_And.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2018-11-30
