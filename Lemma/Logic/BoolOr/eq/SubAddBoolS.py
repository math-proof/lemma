from util import *


@apply
def apply(self):
    b = self.of(Bool)
    p, q = b.of(Or)

    return Equal(self, Bool(p) + Bool(q) - Bool(p & q))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    x = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    Eq << apply(Bool(Or(Element(x, A), Element(x, B))))

    Eq << Eq[0].this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Add(*Eq[-1].rhs.args[:2]).this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].this.rhs.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].this.rhs.apply(Algebra.AddIteS.eq.IteAnd)

    Eq << Bool(Element(x, A & B)).this.apply(Logic.Bool.eq.Ite)

    Eq << Eq[-2] - Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.AddIteS.eq.IteAnd)

    Eq << Eq[1].subs(Eq[-1])

    Eq << Eq[-1].this.find(Or).simplify()


if __name__ == '__main__':
    run()

# created on 2018-02-24
