from util import *


@apply
def apply(given):
    or_eqs = given.of(Or)

    common_term = None
    for eq in or_eqs:
        x, y = eq.of(Equal)
        if common_term is None:
            common_term = {x, y}
        else:
            common_term &= {x, y}
    if len(common_term) == 1:
        x, *_ = common_term

        rhs = set()
        for eq in or_eqs:
            s = {*eq.args}
            s.remove(x)
            rhs |= s

        return Element(x, FiniteSet(*rhs))


@prove
def prove(Eq):
    from Lemma import Set

    x, a, b, c = Symbol(real=True, given=True)
    Eq << apply(Equal(x, a) | Equal(x, b) | Equal(x, c))

    Eq << Set.Or.Eq.of.In_Finset.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2018-11-19
