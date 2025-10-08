from util import *


@apply
def apply(given, index=0):
    from sympy.concrete.limits import limits_dict
    function, *limits = given.of(All)
    limit = limits.pop(index)

    limitsDict = limits_dict([limit])
    eqs = []
    for var, domain in limitsDict.items():
        if isinstance(domain, list):
            cond = conditionset.conditionset(var, *domain).simplify()
        elif domain.is_set:
            cond = Element(var, domain).simplify()
        else:
            assert domain.is_bool
            cond = domain
        eqs.append(cond.invert().simplify())

    if function.is_Or:
        eqs += function.args
    else:
        eqs.append(function)

    if limits:
        return All(Or(*eqs), *limits)
    return Or(*eqs)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    x, y = Symbol(integer=True)
    f = Function(shape=(), integer=True)
    A, B = Symbol(etype=dtype.integer)

    Eq << apply(All[x:A, y:B](f(x, y) > 0), index=1)

    Eq << Bool.All.given.All_Or_Not.apply(Eq[1])

    Eq << Bool.Or_Not.of.All.apply(Eq[0])
#


if __name__ == '__main__':
    run()

# created on 2018-12-19
