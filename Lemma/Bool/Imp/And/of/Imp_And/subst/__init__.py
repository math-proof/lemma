from util import *


@apply
def apply(given, index=None):
    et, f = given.of(Imply)
    eqs = et.of(And)
    if index is None:
        for index, eq in enumerate(eqs):
            if eq.is_Equal:
                break

    eq = eqs[index]
    old, new = eq.of(Equal)

    return Imply(et, f._subs(old, new))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Bool

    x, y = Symbol(integer=True)
    t, f, g = Function(integer=True)
    Eq << apply(Imply(Equal(t(x), y) & (f(x) > y), Equal(f(t(x), y), g(x))))

    Eq << Bool.Imp_And.of.ImpAnd.apply(Eq[0])

    Eq << Eq[-1].this.rhs.args[:2].apply(Bool.UFn.of.UFn.Eq, swap=True)




if __name__ == '__main__':
    run()
# created on 2023-04-25
# updated on 2023-05-13
del Bool
from . import Bool
