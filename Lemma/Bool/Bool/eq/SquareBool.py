from util import *


@apply
def apply(self):
    assert self.is_Bool
    return Equal(self, self * self)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Nat

    x, y = Symbol(real=True)
    Eq << apply(Bool(x > y))

    b = Symbol(Eq[0].lhs)
    Eq << Or(Equal(b, 0), Equal(b, 1), plausible=True)

    Eq << Eq[-1].this.args[0].lhs.definition

    Eq << Eq[-1].this.args[0].lhs.definition

    Eq << Set.Bool.In.Finset.apply(Eq[0].lhs)

    Eq << Set.OrEqS.of.In_Finset.apply(Eq[-1])

    Eq << Nat.Mul.eq.Zero.of.OrEqS.apply(Eq[1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.base.definition




if __name__ == '__main__':
    run()

# created on 2018-03-10
# updated on 2023-06-18
