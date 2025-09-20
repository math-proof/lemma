from util import *


@apply
def apply(self):
    arg = self.of(Re)
    return Equal(self, Re(~arg))


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(complex=True, shape=(n,))
    Eq << apply(Re(x * y))

    z = Symbol(x * y)
    Eq << z.this.definition

    Eq << Algebra.EqConj.of.Eq.apply(Eq[-1])

    Eq << Eq[0].subs(Eq[1].reversed, Eq[2].reversed)



if __name__ == '__main__':
    run()
# created on 2023-06-24
