from util import *


@apply
def apply(is_positive, x=None, w=None, i=None, n=None):
    fx, (x_, S[2]) = is_positive.of(Derivative > 0)

    domain = x_.domain
    assert domain.is_open
    if x is None:
        x = Symbol(shape=(oo,), domain=domain)

    if w is None:
        w = Symbol(shape=(oo,), real=True)

    if i is None:
        i = Symbol(integer=True)

    if n is None:
        n = Symbol(integer=True, positive=True)

    assert x.domain_assumed == domain
    return Imply(Equal(Sum[i:n](w[i]), 1) & All[i:n](w[i] >= 0), GreaterEqual(Sum[i:n](w[i] * fx._subs(x_, x[i])), fx._subs(x_, Sum[i:n](w[i] * x[i]))))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Calculus, Bool, Finset, Nat

    n = Symbol(integer=True, positive=True, given=False)
    a, b = Symbol(real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    x = Symbol(domain=domain)
    w = Symbol(shape=(oo,), real=True)
    f = Function(real=True)
    Eq << apply(Derivative(f(x), (x, 2)) > 0, w=w, n=n)

    Eq.initial = Eq[1].subs(n, 1)

    Eq << Eq.initial.this.lhs.apply(Bool.Cond.of.Eq.Cond.subst, ret=0)

    Eq << Bool.Imp.given.ImpEq.apply(Eq[-1])

    Eq.induct = Eq[1].subs(n, n + 1)

    Eq << Eq.induct.this.rhs.find(Sum).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.find(f[~Sum]).apply(Algebra.Sum.eq.Add.pop)

    Eq.lt, Eq.ge = Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=w[n] < 1)

    Eq << Eq.ge.this.apply(Bool.Imp.flatten)

    Eq << Eq[-1].this.lhs.apply(Algebra.EqAll_Eq_0.of.Eq_Sum.Ge.All_Ge_0.squeeze)

    Eq << Bool.Imp_And.given.Imp.And.subst.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Bool.Cond.of.And, index=1)

    i = Eq[-1].lhs.variable
    fxi = Eq[-1].rhs.find(Sum, f)
    Eq << Eq[-1].lhs.this.apply(Algebra.Sum.eq.Zero.Mul.of.All_Eq_0, Stack[i:n](fxi))

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Nat.Eq.UFn.given.Eq.UFn)

    Eq << Bool.Imp_And.given.Imp.Imp.apply(Eq[-1])

    x = fxi.arg.base
    Eq << Eq[-1].lhs.this.apply(Algebra.Sum.eq.Zero.Mul.of.All_Eq_0, x)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Nat.Eq.UFn.given.Eq.UFn)

    Eq << Eq.lt.this.apply(Bool.Imp.flatten)

    Eq << Eq[-1].this.find(Sum).apply(Finset.Sum.eq.AddSumS, cond={n})

    Eq << Eq[-1].this.find(Equal) - w[n]

    Eq << Eq[-1].this.find(Less) - w[n]

    Eq << Eq[-1].this.apply(Bool.Imp.fold, index=2)

    Eq << Eq[-1].this.find(And).apply(Algebra.EqDiv.of.Gt_0.Eq, simplify=None, ret=1)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(Finset.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-1].this.lhs.apply(Bool.All.All.of.All, cond={n})

    Eq << Eq[-1].this.apply(Bool.Imp.fold)

    Eq << Eq[-1].this.rhs.apply(Bool.Imp.flatten)

    Eq << Eq[-1].this.rhs.apply(Bool.Imp.fold, index=slice(1, None))

    Eq << Eq[-1].this.find(And).apply(Algebra.All.And.of.Cond.All, simplify=None)

    Eq << Eq[-1].this.find(And).apply(Algebra.GeDiv.of.Gt_0.Ge, ret=0)

    Eq << Eq[-1].this.rhs.apply(Bool.Imp.flatten)

    Eq << Eq[-1].this.rhs.apply(Bool.Imp.fold, 1)

    Eq << Eq[-1].this.apply(Bool.Imp.flatten)

    w_ = Symbol('w', Stack[i:n](w[i] / (1 - w[n])))
    Eq << w_[i].this.definition * (1 - w[n])

    Eq << Eq[-1].reversed

    Eq << Algebra.Cond.given.And.subst.apply(Eq[-3], *Eq[-1].args, simplify=None)

    Eq << Eq[-1].this.find(Equal & ~GreaterEqual).apply(Algebra.All.of.Cond.domain_defined, wrt=i)

    Eq.induct1 = Eq[-1].this.lhs.apply(Set.In.Icc.of.Lt.Ge)

    Eq << Algebra.Cond.of.Cond.subst.apply(Eq[1], w[:n], w_)

    Eq << Eq[-1].this.find(Sum).simplify()

    Eq << Eq[-1].this.find(~Sum >= f).simplify()

    Eq << Eq[-1].this.find(f[~Sum]).simplify()

    Eq << Bool.Imp.of.Cond.apply(Eq[-1], cond=Eq.induct1.lhs)

    Eq << Eq[-1].this.apply(Bool.Imp_Imp.Is.Imp_Imp.And)

    Eq <<  Eq[-1].this.find(And[~Element]).apply(Set.Lt.of.In_Icc)

    Eq << Eq[-1].this.find(And[Less]).apply(Algebra.GeMul.of.Lt.Ge)

    Eq.hypothesis = Eq[-1].this.find(GreaterEqual[Mul]) + w[n] * f(x[n])

    Eq << Bool.Imp.of.Cond.apply(Eq[0], cond=Eq.induct1.lhs)

    Eq << Eq[-1].this.find(Greater).apply(Bool.All.of.Cond, Eq[-1].find(Derivative).variable)

    Eq << Bool.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Element(x[n], domain, plausible=True)

    Eq << Bool.Imp.of.Cond.apply(Eq[-1], cond=Eq[-2].lhs)

    Eq <<= Eq[-3] & Eq[-1]

    Eq.suffices = Eq[-1].this.rhs.apply(Bool.Imp.of.Cond, cond=Eq.induct1.rhs.lhs)

    Eq << Element(x[i], domain, plausible=True)

    Eq << Bool.Imp.of.Cond.apply(Eq[-1], cond=Eq.induct1.rhs.lhs)

    Eq << Bool.Imp_And.of.ImpAnd.apply(Eq[-1], index=1)

    Eq << Eq[-1].this.rhs.apply(Algebra.All.And.of.Cond.All, simplify=None)

    Eq << Bool.Imp_And.of.ImpAnd.apply(Eq[-1], index=0)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.limits.domain_defined)

    Eq << Eq[-1].this.rhs.apply(Set.In.of.Eq_Sum.All.mean)

    Eq << Bool.Imp.of.Cond.apply(Eq[-1], cond=Eq.suffices.lhs)

    Eq <<= Eq.suffices & Eq[-1]

    Eq << Eq[-1].this.rhs.rhs.apply(Calculus.Ge.of.In.In.In.All_Gt_0.Jesson)

    Eq << Eq[-1].this.find(Sum[Mul]).simplify()

    Eq << Eq[-1].this.find(Sum[Mul, Tuple[0]]).simplify()

    Eq <<= Eq.hypothesis & Eq[-1]

    Eq << Eq[-1].this.find(GreaterEqual & GreaterEqual).apply(Nat.Ge.of.Ge.Ge)

    Eq << Imply(Eq[1], Eq.induct, plausible=True)

    Eq << Bool.Cond.of.Cond.All_Imp.apply(Eq.initial, Eq[-1], n=n, start=1)





if __name__ == '__main__':
    run()
# created on 2020-06-01
# updated on 2023-08-26
