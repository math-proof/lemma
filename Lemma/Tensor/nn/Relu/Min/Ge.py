from util import *


@apply
def apply(x, y, z):
    return GreaterEqual(relu(x - y) + Min(y, z), Min(x, z))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x, y, z)

    Eq << Eq[0].this.find(relu).defun()


    Eq << Eq[-1].this.lhs.args[0].apply(Algebra.Max.eq.Ite)

    Eq << Eq[-1].this.lhs.apply(Algebra.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.lhs.args[1].expr.apply(Algebra.Add.eq.Min)

    Eq << Eq[-1].this.lhs.args[0].cond.reversed

    Eq << Eq[-1].apply(Logic.Cond.given.Or.OrNot, cond=x - y <= 0)

    Eq << Logic.And_And.given.And.Cond.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].apply(Logic.BFn.of.BFnIte.Cond, swap=True, ret=1), Eq[-1].apply(Logic.BFn.of.BFnIte.Cond, invert=True, swap=True, ret=1)

    Eq <<= Eq[-2].this.args[1] + y, Eq[-1].this.args[1] + z

    Eq << Eq[-1].this.args[1].apply(Algebra.GeMin.of.Gt, x)

    Eq << Eq[-2].this.args[1].apply(Algebra.LeMin.of.Le, z)





if __name__ == '__main__':
    run()
# created on 2020-12-27
# updated on 2022-01-08
