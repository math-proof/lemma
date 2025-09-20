from util import *


@apply
def apply(given, *limits):
    fx = given.of(Expr <= 0)
    for limit in limits:
        x = limit[0]
        assert fx._has(x)
        assert not x.is_given
        assert not x.is_integer
        x, domain, *dir = Tuple(*limit).coerce_setlimit()
        if dir:
            dir, = dir
            assert dir > 0
        domain_defined = fx.domain_defined(x)
        assert domain in domain_defined

    return Integral(fx, *limits) <= 0


@prove
def prove(Eq):
    from Lemma import Calculus

    t = Symbol(real=True, positive=True)
    x = Symbol(real=True)
    f = Function(real=True, continuous=True)
    Eq << apply(f(x) <= 0, (x, 0, t))

    Eq << -Eq[0]

    Eq << Calculus.Ge_0.Integral.of.Ge_0.apply(Eq[-1], (x, 0, t))

    Eq << -Eq[-1]

    Eq << Eq[-1].this.find(Integral).simplify()




if __name__ == '__main__':
    run()
# created on 2023-03-25
