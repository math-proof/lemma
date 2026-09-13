from util import *


def probability_limits(condition, **kwargs):
    if condition.is_And:
        limits = []
        for cond in condition.args:
            limits += probability_limits(cond, **kwargs)

        return limits
    elif condition.is_Equal:
        ...
    elif condition.is_Relational:
        expr = condition.lhs - condition.rhs
        rvs = expr.random_symbols
        if len(rvs) > 1:
            return

        x, = rvs
        domain = condition.domain_conditioned(x)
        if domain.is_Interval:
            a, b = domain.args
            return [(x.var, a, b)]

def compute_density(condition):
    limits = probability_limits(condition)
    ps = pspace(condition)

    cond = S.true
    for var, sym in ps.values2symbols().items():
        assert pspace(var).is_Continuous
        cond &= Equal(var, sym)

    return Integral(Pr(cond), *limits)


@apply
def apply(self):
    condition = self.of(Pr)
    return Equal(self, compute_density(condition))


@prove(provable=False)
def prove(Eq):
    x, y = Symbol(real=True, random=True)
    a, b = Symbol(real=True)
    Eq << apply(Pr((x >= a) & (y <= b)))




if __name__ == '__main__':
    run()
# created on 2023-03-20
from . import joint
