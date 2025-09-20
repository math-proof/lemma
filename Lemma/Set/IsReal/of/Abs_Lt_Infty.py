from util import *


@apply
def apply(self):
    x = self.of(Abs < Infinity)
    assert x.is_extended_real
    return Element(x, Interval(-oo, oo))


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(extended_real=True)
    Eq << apply(Abs(x) < oo)

    Eq << Eq[0].this.apply(Set.Abs_Lt_Infty.Is.IsReal)


if __name__ == '__main__':
    run()
# created on 2023-04-16
