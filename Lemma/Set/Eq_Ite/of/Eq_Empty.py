from util import *


@apply
def apply(given, peicewise_A, peicewise_B):
    AB = given.of(Equal[EmptySet])
    A, B = AB.of(Intersection)

    (fx, c0_A), (_fx, S[True]) = peicewise_A.of(Piecewise)
    (gx, c0_B), (_gx, S[True]) = peicewise_B.of(Piecewise)

    x, _A = c0_A.of(Element)
    S[x], _B = c0_B.of(Element)

    if A != _A:
        S[A], B = B, A

    assert B == _B

    return Equal(peicewise_A + peicewise_B, Piecewise((fx + _gx, Element(x, A)),
                                                      (_fx + gx, Element(x, B)),
                                                      (_fx + _gx, True)))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Nat

    A, B = Symbol(etype=dtype.integer)
    x = Symbol(integer=True)
    f, g = Function(shape=(), integer=True)
    f_quote = Function("f'", shape=(), integer=True)
    g_quote = Function("g'", shape=(), integer=True)
    Eq << apply(Equal(A & B, A.etype.emptySet),
        Piecewise((f(x), Element(x, A)), (f_quote(x), True)),
        Piecewise((g(x), Element(x, B)), (g_quote(x), True)))

    Eq << Eq[1].this.lhs.apply(Nat.AddIteS.eq.IteAnd)

    Eq << Eq[-1].apply(Bool.All.given.All.AllNot, cond=Element(x, A))

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq <<= Eq[-2].this().expr.simplify(), Eq[-1].this().expr.simplify()



    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

# created on 2020-07-04
