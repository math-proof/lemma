from util import *

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    boole, S[2] = self.of(Pow)
    assert boole.is_Bool
    return Equal(self, boole)


@prove
def prove(Eq):
    from Lemma import Bool
    x, y = Symbol(real=True)

    Eq << apply((x > y).toNat ** 2)

    Eq << Eq[0].this.rhs.apply(Bool.Bool.eq.SquareBool)


if __name__ == '__main__':
    run()

# created on 2018-03-11
