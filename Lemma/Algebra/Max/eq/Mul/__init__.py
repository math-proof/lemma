from util import *


@apply
def apply(self):
    args = self.of(Max)

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
        if factor > 0:
            args = [arg / factor for arg in args]
            return Equal(self, factor * Max(*args))


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x, y = Symbol(real=True)
    r = Symbol(real=True, positive=True)
    Eq << apply(Max(x * r, y * r))

    Eq << Eq[0].this.lhs.apply(Nat.Max.eq.IteGe)

    Eq << Eq[-1].this.rhs.args[1].apply(Nat.Max.eq.IteGe)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ite.eq.Mul)




if __name__ == '__main__':
    run()
# created on 2019-08-17
del Min
from . import Min
from . import of
