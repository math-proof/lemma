from util import *


@apply
def apply(cond, forall):
    if cond.is_Quantifier:
        assert not cond.variables_set & forall.variables_set

    fn, *limits = forall.of(All)
    return All(cond & fn, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    y = Symbol(real=True)
    B = Symbol(etype=dtype.real)
    f, g = Function(integer=True)
    Eq << apply(f(y) > 0, All[y:B](g(y) > 0))

    Eq << Bool.All_And.given.All.All.apply(Eq[-1])

    Eq << Algebra.All.given.Cond.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-12-24
