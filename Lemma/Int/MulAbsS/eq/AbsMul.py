from util import *


@apply
def apply(self, evaluate=False):
    args = []

    for arg in self.of(Mul):
        if arg.is_Abs:
            args.append(arg.of(Abs))
            continue
        elif arg.is_Pow:
            if arg.base.is_Abs and arg.exp.is_integer:
                args.append(Pow(arg.base.of(Abs), arg.exp))
                continue

        assert arg >= 0
        args.append(arg)

    return Equal(self, Abs(Mul(*args), evaluate=evaluate))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Int, Int, Nat

    x, y = Symbol(real=True)
    Eq << apply(abs(x) * abs(y))

    Eq << Eq[-1].this.lhs.find(Abs).apply(Int.Abs.eq.IteGe_0)

    Eq << Eq[-1].this.lhs.find(Abs).apply(Int.Abs.eq.IteGe_0)

    Eq << Eq[-1].this.lhs.apply(Nat.Mul_Ite.eq.Ite_MulS)

    Eq << Eq[-1].this.lhs.apply(Bool.Ite_Ite.eq.Ite__Ite)

    Eq << Eq[-1].this.lhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, -2)

    Eq << Eq[-1].this.lhs.args[0].cond.apply(Bool.And_Or.Is.OrAndS)

    Eq << Eq[-1].this.lhs.args[0].expr.apply(Nat.Mul.eq.IteAndNeS_0)

    Eq << Eq[-1].this.lhs.apply(Bool.Ite_Ite.eq.Ite__Ite, index=0)

    Eq << Eq[-1].this.lhs.args[0].cond.apply(Bool.And_Or.Is.OrAndS)

    Eq << Eq[-1].this.lhs.apply(Bool.Ite__Ite.eq.Ite__IteAnd_Not, 0)

    Eq.equal = Eq[-1].this.lhs.args[1].cond.apply(Bool.And_Or.Is.OrAndS)

    Eq.suffice = Imply(Eq.equal.lhs.args[1].cond, Equal(x * y, 0), plausible=True)

    Eq << Bool.ImpOr.given.Imp.Imp.apply(Eq.suffice)

    Eq <<= Eq[-1].this.lhs.apply(Bool.Cond.of.And, index=0), Eq[-2].this.lhs.apply(Bool.Cond.of.And, index=0)

    Eq << Eq[-2].this.lhs * x

    Eq << Eq[-1].this.lhs * y

    Eq << -Eq.suffice.this.rhs

    Eq << Eq[-1].apply(Bool.Iff_And.of.Imp)

    Eq << Bool.EqIteS.of.Iff.subst.apply(Eq[-1], Eq.equal.lhs)

    Eq << Eq[-1].this.rhs.apply(Bool.Ite.subst, index=1, reverse=True)

    Eq << Eq.equal.this.lhs.subs(Eq[-1])

    Eq.equal = Eq[-1].this.rhs.apply(Int.Abs.eq.IteGt_0)

    Eq.equivalent = Iff(Eq.equal.lhs.args[0].cond, Eq.equal.rhs.args[0].cond, plausible=True)

    Eq.suffice, Eq.necessary = Bool.Iff.given.Imp.Imp.apply(Eq.equivalent)

    Eq << Bool.ImpOr.given.Imp.Imp.apply(Eq.suffice)

    Eq << Eq[-2].this.lhs.apply(Int.Gt_0.of.Lt_0.Lt_0)

    Eq << Eq[-1].this.lhs.apply(Nat.Gt_0.of.Gt_0.Gt_0)

    Eq << Eq.necessary.this.lhs.apply(Int.AndGtS_0.ou.AndLtS_0.of.Mul.gt.Zero)

    Eq << Bool.EqIteS.of.Iff.subst.apply(Eq.equivalent, Eq.equal.lhs)


if __name__ == '__main__':
    run()

# created on 2018-02-11
# updated on 2023-05-19
