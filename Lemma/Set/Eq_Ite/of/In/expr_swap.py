from util import *


@apply
def apply(given, piecewise):
    x, U = given.of(Element)
    ec = piecewise.of(Piecewise)
    S[x], s = ec[0].cond.of(Element)
    assert s in U
    f = ec[0].expr
    g = ec[1].expr

    return Equal(piecewise, Piecewise((g, Element(x, U - s)), (f, True)).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x = Symbol(integer=True, given=True)
    S, A = Symbol(etype=dtype.integer, given=True)
    s = Symbol(A & S)
    f, g = Function(shape=())
    Eq << apply(Element(x, S), Piecewise((f(x), Element(x, s)), (g(x), True)))

    Eq << Bool.Ite__Ite.eq.IteAnd_Not__Ite.apply(Eq[2].lhs)

    (gx, cond_contains), (fx, _) = Eq[-1].rhs.args
    p = Symbol(Piecewise((gx, Equal((cond_contains).toNat, 1)), (fx, _)))
    (gx, cond_notcontains), (fx, _) = Eq[2].rhs.args
    q = Symbol(Piecewise((gx, Equal((cond_notcontains).toNat, 1)), (fx, _)))
    Eq << p.this.definition

    Eq.p_definition = Eq[-1].this.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    Eq << Eq[2].subs(Eq.p_definition.reversed)

    Eq.q_definition = q.this.definition

    Eq << Eq.q_definition.this.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq.bool_equality = Equal(cond_contains.toNat, cond_notcontains.toNat, plausible=True)

    Eq << Eq.bool_equality.this.rhs.apply(Bool.Bool.eq.Ite)

    Eq << Eq[-1].apply(Bool.Cond.given.Or.OrNot, cond=cond_contains)

    Eq.all_not_s, Eq.all_s = Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq << ~Eq.all_not_s

    Eq << Eq[-1].this.apply(Bool.BFn.of.BFnIte.Cond, swap=True, ret=1)

    Eq << Eq[-1].this.args[0].simplify()

    Eq <<= Eq[-1] & Eq[0]

    Eq << ~Eq.all_s

    Eq << Eq[-1].this.apply(Bool.BFn.of.BFnIte.Cond, swap=True, invert=True, ret=1)

    Eq << Eq[-1].this.args[0].simplify()

    Eq << Eq.q_definition.subs(Eq.bool_equality.reversed)

    Eq << Eq[-1].this.find(Equal).apply(Algebra.Eq_Bool.Is.Cond)

    Eq << Eq.p_definition.subs(Eq[-1].reversed)





if __name__ == '__main__':
    run()

# created on 2020-10-27
# updated on 2023-05-20
