from util import *


@apply
def apply(ne_zero, eq, *, simplify=True):
    x = ne_zero.of(Unequal[0])
    lhs, rhs = eq.of(Equal)
    if simplify and lhs.is_Add:
        lhs = Add(*(a / x for a in lhs.args))
    else:
        lhs /= x

    if simplify and rhs.is_Add:
        rhs = Add(*(a / x for a in rhs.args))
    else:
        rhs /= x
    return Equal(lhs, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(real=True, given=True)
    f, g, h = Function(real=True)
    Eq << apply(Unequal(f(x), 0), Equal(g(x) * f(x), h(x) * f(x) + x))

    Eq << Eq[1] / f(x)

    Eq << Logic.Cond.of.Or_Not.Cond.apply(Eq[0], Eq[-1])

    Eq << Eq[2].this.rhs.ratsimp()





if __name__ == '__main__':
    run()

# created on 2018-01-24
# updated on 2023-05-02
