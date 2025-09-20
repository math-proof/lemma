from util import *


@apply
def apply(self, factor=None):
    args = self.of(Min)

    if factor is None:
        common_factors = None

        for arg in args:
            if not arg.is_Mul:
                return

            if common_factors is None:
                common_factors = {*arg.args}
            else:
                common_factors &= {*arg.args}

        if common_factors:
            factor = Mul(*common_factors)

    assert factor <= 0
    args = [arg / factor for arg in args]
    return Equal(self, factor * Max(*args))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True)
    r = Symbol(real=True, negative=True)
    Eq << apply(Min(x * r, y * r))

    Eq << Eq[0].this.lhs.apply(Algebra.Min.eq.IteLe)

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Max.eq.Ite)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ite.eq.Mul)

    Eq << Eq[-1].this.find(LessEqual).reversed




if __name__ == '__main__':
    run()
# created on 2020-01-26
# updated on 2023-03-26
from . import of
