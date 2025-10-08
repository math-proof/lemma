from util import *


@apply
def apply(cond, forall):
    if cond.is_Quantifier:
        assert not cond.variables_set & forall.variables_set

    fn, *limits = forall.of(All)
    assert not cond.has(*forall.variables)
    assert Tuple.is_nonemptyset(limits)
    return All(cond & fn, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y = Symbol(real=True)
    B = Symbol(etype=dtype.real, empty=False)
    f, g = Function(integer=True)
    Eq << apply(f(x) > 0, All[y:B](g(y) > 0))

    Eq << Bool.All.All.of.All_And.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-06-06
