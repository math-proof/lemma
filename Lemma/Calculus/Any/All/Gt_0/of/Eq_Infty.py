from util import *


@apply
def apply(eq, delta=None):
    fx, (x, x0) = eq.of(Equal[Limit, oo])
    if isinstance(delta, str):
        var = delta
    elif delta is None:
        var = 'delta'

    if not isinstance(delta, Basic):
        delta = eq.generate_var(positive=True, var=var)

    x0, epsilon = x0.clear_infinitesimal()
    if epsilon > 0:
        cond = Interval.open(x0, x0 + delta)
    elif epsilon < 0:
        cond = Interval.open(x0 - delta, x0)
    else:
        cond = (abs(x - x0) > 0) & (abs(x - x0) < delta)
    return Any[delta](All[x:cond](fx > 0))


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra

    x, x0 = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(Limit[x:x0](f(x)), oo))

    epsilon = Symbol(positive=True)
    delta = Eq[-1].variable
    Eq << Calculus.Any.All.of.Eq_Limit.limit_definition.apply(Eq[0], epsilon, delta)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt.of.Gt.relax, lower=0)












if __name__ == '__main__':
    run()
# created on 2023-10-15
