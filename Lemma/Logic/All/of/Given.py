from util import *



@apply
def apply(given, wrt=None):
    fn1, fn = given.of(Given)
    if wrt is None:
        wrt = fn.wrt
    return All[wrt:fn](fn1)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(Given(Equal(f[n + 1], g[n + 1]), Equal(f[n], g[n])), wrt=n)

    Eq << Eq[0].apply(Logic.Or_Not.of.Imp)

    Eq << Logic.All.of.All_OrNot.apply(Eq[-1], pivot=1, wrt=n)


if __name__ == '__main__':
    run()
# created on 2018-09-19
