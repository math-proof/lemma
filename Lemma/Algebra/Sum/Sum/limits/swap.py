from util import *


@apply
def apply(self):
    [*args], *limits = self.of(Sum[Mul])

    for index in range(len(args)):
        if args[index].is_Sum:
            break
    else:
        return

    sgm = args.pop(index)
    if isinstance(sgm.expr, Mul):
        args.extend(sgm.expr.args)
    else:
        args.append(sgm.expr)

    function = Mul(*args).powsimp()
    independent, dependent = function.as_independent(*(x for x, *_ in self.limits), as_Add=False)
    if independent == S.One:
        rhs = sgm.func(Sum(function, *limits), *sgm.limits)
    else:
        rhs = sgm.func(independent * Sum(dependent, *limits), *sgm.limits)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Finset

    i, j = Symbol(integer=True)
    n, m = Symbol(integer=True, positive=True)
    g = Symbol(shape=(oo, oo), real=True)
    h = Symbol(shape=(oo,), real=True)
    Eq << apply(Sum[i:m](h[i] * Sum[j:n](g[i, j])))

    Eq << Eq[0].this.lhs.expr.apply(Finset.Mul_Sum.eq.Sum_Mul)
    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.swap)


if __name__ == '__main__':
    run()
# created on 2020-03-28
