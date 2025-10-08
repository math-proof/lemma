from util import *


def limits_dependent(limits_x, limits_y, dir=None):
    from sympy.concrete.limits import limits_dict
    dict_x = limits_dict(limits_x)
    dict_y = limits_dict(limits_y)
    if dict_x.keys() & dict_y.keys():
        return True

    for x, domain_x in dict_x.items():
        for y, domain_y in dict_y.items():
            if domain_y is None:
                ...
            elif isinstance(domain_y, list):
                if any(d._has(x) for d in domain_y):
                    return True
            elif domain_y.is_set:
                if domain_y._has(x):
                    return True

            if dir:
                continue

            if domain_x is None:
                ...
            elif isinstance(domain_x, list):
                if any(d._has(x) for d in domain_x):
                    return True
            elif domain_x.is_set:
                if domain_x._has(y):
                    return True

    return False

@apply
def apply(forall, exists):
    fx, *limits_f = forall.of(All)
    fy, *limits_e = exists.of(Any)

    assert not limits_dependent(limits_f, limits_e, dir=True)
    return Any(All(fx & fy, *limits_f), *limits_e)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    y, x, z = Symbol(real=True)
    f, g, h = Function(integer=True)
    Eq << apply(All[z:h(z) > y](h(y, z) > 0), Any[y:g(y) > 1, x:f(x) > 0](g(x) > 0))

    Eq << Eq[-1].this.expr.apply(Bool.All_And.given.All.All)

    Eq << Eq[-1].this.find(Or).apply(Bool.Or.given.Cond, 0)

    Eq << Bool.Any_And.of.Any.All.apply(Eq[0], Eq[1])


if __name__ == '__main__':
    run()

# created on 2018-12-04
