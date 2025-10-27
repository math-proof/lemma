from util import *


@apply
def apply(self):
    b = self.of(Bool)
    p, q = b.of(Or)

    return Equal(self, Bool(p) + Bool(q) - Bool(p & q))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Nat
    x = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    Eq << apply(functions.Bool(Or(Element(x, A), Element(x, B))))

    Eq << Eq[0].this.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    Eq << Add(*Eq[-1].rhs.args[:2]).this.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    Eq << Eq[-1].this.rhs.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    Eq << Eq[-1].this.rhs.apply(Nat.AddIteS.eq.IteAnd)

    Eq << functions.Bool(Element(x, A & B)).this.apply(Bool.Bool.eq.Ite)

    Eq << Eq[-2] - Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Nat.AddIteS.eq.IteAnd)

    Eq << Eq[1].subs(Eq[-1])

    Eq << Eq[-1].this.find(Or).simplify()


if __name__ == '__main__':
    run()

# created on 2018-02-24
