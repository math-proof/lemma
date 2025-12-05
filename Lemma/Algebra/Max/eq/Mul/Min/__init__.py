from util import *


@apply
def apply(self, factor=None):
    args = self.of(Max)

    if factor is None:
        common_factors = None

        for arg in args:
            if not arg.is_Mul:
                common_factors = None
                break

            if common_factors is None:
                common_factors = {*arg.args}
            else:
                common_factors &= {*arg.args}

        if common_factors:
            factor = Mul(*common_factors)
        else:
            factor = -1
    assert factor < 0

    args = [arg / factor for arg in args]
    return Equal(self, factor * Min(*args))


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x, y = Symbol(real=True)
    r = Symbol(real=True, negative=True)
    Eq << apply(Max(x * r, y * r))

    Eq << Eq[0].this.lhs.apply(Nat.Max.eq.IteGe)

    Eq << Eq[-1].this.rhs.args[1].apply(Nat.Min.eq.IteLe)

    Eq << Eq[-1].this.lhs.apply(Nat.Ite_MulS.eq.Mul_Ite)

    Eq << Eq[-1].this.find(GreaterEqual).reversed





if __name__ == '__main__':
    run()
# created on 2020-01-24
# updated on 2023-06-18
from . import of
