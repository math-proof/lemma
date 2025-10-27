from util import *


@apply
def apply(given, var=None):
    S_abs = given.of(Equal[1])
    S = S_abs.of(Card)
    assert S.is_set
    if var is None:
        var = S.element_symbol()
        assert not var.is_set
    return Element(Sum[var:S](var), S)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Nat

    n = Symbol(integer=True)
    S = Symbol(etype=dtype.integer[n])
    Eq << apply(Equal(Card(S), 1))

    Eq << Set.Any.Eq.One.of.Eq.apply(Eq[0]).reversed

    Eq <<= Eq[1] & Eq[-1]

    Eq << Eq[-1].this.apply(Algebra.Cond.Any.given.Any.And, simplify=None)

    Eq << Eq[-1].this.expr.apply(Nat.Eq.UnaryFn.given.Eq.UnaryFn)




if __name__ == '__main__':
    run()

# created on 2020-07-21
# updated on 2023-08-26
