from util import *


def difference_of_domain_defined(domain_defined, _domain_defined, limitsDict):
    keys = domain_defined.keys()
    diff_set = {}
    for key in keys:
        domain = domain_defined[key]
        _domain = _domain_defined[key]
        domain_limited = limitsDict[key]
        if _domain != domain:
            if domain in _domain:
                if domain_limited != domain:
                    if _domain - domain & domain_limited:
# consider the case:
# _domain = [0; n)
# domain = [1; n)
# domain_limited = [1; t + 1)
                        diff_set[key] = domain & domain_limited
                else:
                    diff_set[key] = domain

    return diff_set


def associate(Sum, self, simplify=True):
    from sympy.concrete.limits import limits_dictionary, limits_update
    args = []
    function, *limits = self.of(Sum)
    limits = tuple(limits)
    domain_defined = function.domain_defined_for_limits(limits)

    limitsDict = limits_dictionary(limits)

    for arg in function.of(Sum.operator):
        arg_domain_defined = arg.domain_defined_for_limits(limits)
        diff_set = difference_of_domain_defined(domain_defined, arg_domain_defined, limitsDict)
        if diff_set:
            _limits = limits_update(limits, diff_set)
        else:
            _limits = limits
        arg = Sum(arg, *_limits)

        if simplify:
            arg = arg.simplify()
        args.append(arg)

    return Sum.operator(*args, evaluate=False)


@apply
def apply(self, simplify=True):
    return Equal(self, associate(Sum, self, simplify=simplify), evaluate=False)


@prove(provable=False)
def prove(Eq):
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, h = Function(real=True)
    Eq << apply(Sum[i:n](f(i) + h(i)))




if __name__ == '__main__':
    run()

# created on 2018-02-20
# updated on 2023-06-02
