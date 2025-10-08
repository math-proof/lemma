from util import *


def collect(given, cond=None):
    or_eqs = given.of(Or)

    new_or_eqs = []

    and_eqs = []
    for and_eq in or_eqs:
        if and_eq.is_And:
            try:
                i = and_eq.args.index(cond)
                args = [*and_eq.args]
                del args[i]
                and_eqs.append(And(*args))
                continue
            except:
                ...
        new_or_eqs.append(and_eq)

    if and_eqs:
        new_or_eqs.append(And(Or(*and_eqs), cond))
        return Or(*new_or_eqs)


@apply
def apply(given, *, cond=None):
    return collect(given, cond)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y = Symbol(real=True, given=True)
    f, h, g = Function(real=True)
    Eq << apply(Unequal(x, y) | Equal(f(x), g(y)) & (y > 0) | Equal(h(x), g(y)) & (y > 0), cond=y > 0)

    Eq << Eq[1].this.find(And).apply(Bool.Cond.Or.given.OrAndS, simplify=None)




if __name__ == '__main__':
    run()

# created on 2018-01-15
# updated on 2023-05-12
