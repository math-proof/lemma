from util import *


@apply
def apply(given, index=-1):
    eqs, *limits = given.of(All[And])
    if index is None:
        return tuple(All(eq, *limits) for eq in eqs)
    former, latter = std.array_split(eqs, index)
    former = And(*former)
    latter = And(*latter)
    return All(former, *limits), All(latter, *limits)



@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, c, d = Symbol(real=True)
    a, b = Symbol(real=True, given=True)
    f = Function(shape=(), real=True)
    Eq << apply(All[x:a:b]((x <= c) & (f(x) >= d)))

    Eq << Logic.All.of.All_And.apply(Eq[0], 0)

    Eq << Logic.All.of.All_And.apply(Eq[0], 1)





if __name__ == '__main__':
    run()
# created on 2018-10-01
# updated on 2023-06-05
