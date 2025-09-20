from util import *


@apply
def apply(given):
    assert given.expr.is_And

    limits_dict = given.limits_dict
    for i, eq in enumerate(given.expr.args):
        if eq.is_Equal:
            if eq.lhs in limits_dict:
                old, new = eq.args
            elif eq.rhs in limits_dict:
                new, old = eq.args
            else:
                continue

            limits = given.limits_delete(old)
            if any(limit._has(old) for limit in limits):
                continue

            eqs = [*given.expr.args]
            del eqs[i]
            eqs = [eq._subs(old, new) for eq in eqs]

            domain = limits_dict[old]
            if domain is None:
                limit = (old,)
            else:
                assert not isinstance(domain, list)
                limit = (old, domain)
            eq = given.func(eq, limit).simplify()
            eqs.append(eq)

            return Any(And(*eqs), *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n = Symbol(integer=True, positive=True)
    i, k = Symbol(integer=True)
    j = Symbol(domain=Range(k))
    x = Symbol(real=True, shape=(oo,))
    f, g = Function(shape=(), integer=True)
    f_quote = Function("f'", shape=(), integer=True)
    Eq << apply(Any[x[:n]:f(x[:n]) > 0, i:k]((g(i) > f_quote(j, x[:n])) & Equal(i, j)))

    Eq << Eq[0].this.expr.apply(Logic.Cond.of.Eq.Cond.subst)
    Eq << Logic.And_And.of.And.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-02-28
