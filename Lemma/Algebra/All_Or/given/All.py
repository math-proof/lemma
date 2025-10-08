from util import *


@apply
def apply(given, index=0):
    eqs, *limits = given.of(All[Or])

    return All(eqs[index], *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, a, b, c = Symbol(real=True)
    f = Function(shape=(), real=True)
    Eq << apply(All[x:a:b]((x <= c) | (f(x) >= 1)), 1)

    Eq << ~Eq[0]

    Eq << Bool.Any_And.of.Any.All.All_Imp.apply(Eq[1], Eq[-1])




if __name__ == '__main__':
    run()

# created on 2019-02-05
# updated on 2023-05-20
