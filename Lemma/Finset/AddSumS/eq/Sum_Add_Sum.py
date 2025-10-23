from util import *


def piece_together(Sum, self):
    expr = []
    limits = None
    for arg in self.of(Sum.operator):
        arg_expr, *arg_limits = arg.of(Sum)
        if limits is None:
            limits = arg_limits
            func = arg_expr
        else:
            i = -1
            while i >= -len(limits) and i >= -len(arg_limits):
                if limits[i] == arg_limits[i]:
                    i -= 1
                    continue
                else:
                    break

            i += 1

            assert i < 0

            inner_limits, limits = limits[:i], limits[i:]
            _inner_limits = arg_limits[:i]

            if inner_limits:
                expr = [Sum(f, *inner_limits) for f in expr]

            if _inner_limits:
                func = Sum(arg_expr, *_inner_limits)
            else:
                func = arg_expr

        expr.append(func)

    for limit in limits:
        x, *ab = limit
        if not ab:
            domains = {f.domain_defined(x) for f in expr}
            assert len(domains) == 1, "domains are different:%s" % domains

    return Sum(self.func(*expr), *limits)

@apply
def apply(self):
    [*args] = self.of(Add)
    hit = False
    for i, arg in enumerate(args):
        if arg.is_Mul:
            coeff, (arg_expr, *arg_limits) = arg.of(Expr * Sum)
            arg_expr *= coeff
            args[i] = Sum(arg_expr, *arg_limits)
            hit = True

    if hit:
        rhs = Add(*args)
    else:
        rhs = self

    return Equal(self, piece_together(Sum, rhs))


@prove
def prove(Eq):
    from Lemma import Algebra, Finset, Finset
    i, k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Function(integer=True)
    Eq << apply(Sum[i:k, k:n](f(k, i)) + Sum[k:n](g(k)))

    Eq << Eq[0].this.rhs.apply(Finset.Sum_Add.eq.AddSumS)


if __name__ == '__main__':
    run()

# created on 2018-02-20
