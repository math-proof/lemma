from util import *


def compute_density(condition):
    ps = pspace(condition)
    fx, y = condition.of(Equal)

    cond = S.true
    limits = []
    for var, sym in ps.values2symbols().items():
        assert pspace(var).is_Continuous
        cond &= Equal(var, sym)
        fx = fx._subs(var, sym)
        limits.append((sym,))

    assert not fx.random_symbols

    if y.is_given or not y.is_symbol:
        y = condition.generate_var(real=True)

    return Derivative[y](Integral(Pr(cond) * Bool(LessEqual(fx, y)), *limits))


@apply
def apply(self):
    return Equal(self, compute_density(self.of(Pr)))


@prove(provable=False)
def prove(Eq):
    x, y, z = Symbol(real=True, random=True)
    t = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Pr(Equal(f(x, y, z), t)))


if __name__ == '__main__':
    run()
# created on 2021-07-24
