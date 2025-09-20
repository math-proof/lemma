from util import *


@apply
def apply(given, exclude=None):
    (xi, (i, S[0], n)), S[n] = given.of(Equal[Card[Cup[FiniteSet]]])

    j = xi.generate_var(excludes=exclude, integer=True)
    xj = xi.subs(i, j)

    return All[j:Range(n) - {i}, i:n](Unequal(xi, xj))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic
    n = Symbol(integer=True, positive=True, given=True)
    x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True, given=True)
    Eq << apply(Equal(Card(x[:n].cup_finiteset()), n))

    xi = Eq[1].expr.args[0]
    x, i = xi.args
    b = Symbol(Stack[i:n](x[i].set))
    Eq << Card(Cup[i:n](b[i])).this.arg.expr.definition

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[0], Eq[-1])

    Eq << Sum[i:n](Card(b[i])).this.expr.arg.definition

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[-2], Eq[-1])

    Eq << Set.All_Eq_Empty.SDiff.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.find(Indexed).definition

    Eq << Eq[-1].this.find(Indexed).definition


if __name__ == '__main__':
    run()

# created on 2020-07-19
