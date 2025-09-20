from util import *


@apply
def apply(eq, is_nonzero_real, delta=None):
    A, R = is_nonzero_real.of(Element)
    assert R in Reals - {0}
    fx, (x, x0) = eq.of(Equal[Limit, A])
    if delta is None:
        delta = eq.generate_var(positive=True, var='delta')
    x0, dir = x0.clear_infinitesimal()
    return Any[delta](All[x:(abs(x - x0) > 0) & ((abs(x - x0) < delta))](abs(fx) > abs(A) / 2))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Calculus, Logic

    x, x0 = Symbol(real=True)
    A = Symbol(complex=True)
    f = Function(real=True)
    Eq << apply(Equal(Limit[x:x0](f(x)), A), Element(A, Reals - {0}))

    Eq << Set.Any.Eq.of.In.apply(Eq[1], var='a')

    Eq << Logic.Any_And.of.Any.All.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Logic.Cond.of.Eq.Cond.subst, simplify=None, ret=0)

    Eq << Logic.Any_And.of.AnySetOf.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Set.Ne_0.of.In)

    Eq << Logic.AnySetOf.of.Any_And.apply(Eq[-1], index=0, simplify=None)

    Eq << Eq[-1].this.expr.apply(Calculus.Any.All.Gt.of.Ne_0.Eq_Limit)




if __name__ == '__main__':
    run()
# created on 2020-05-15
# updated on 2023-10-15
