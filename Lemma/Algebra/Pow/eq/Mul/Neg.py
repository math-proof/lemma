from util import *


@apply
def apply(self):
    x, n = self.of(Expr ** Expr)
    assert n.is_integer
    return Equal(self, (-1) ** n * (-x) ** n)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True)
    Eq << apply((x - y) ** 3)

    Eq << Eq[-1].this.lhs.apply(Algebra.Pow.eq.Add)

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Pow.eq.Add)





if __name__ == '__main__':
    run()
# created on 2018-11-14
# updated on 2022-07-08
