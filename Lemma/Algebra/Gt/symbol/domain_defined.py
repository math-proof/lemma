from util import *


@apply
def apply(x):
    domain = x.domain
    assert domain.left_open or domain.right_open
    a, b = domain.of(Interval)
    return Greater(b, a)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, b = Symbol(real=True)
    domain=Interval(a, b, right_open=True)
    x = Symbol(domain=domain)
    Eq << apply(x)

    Eq << Algebra.Lt.symbol.domain_defined.apply(x)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-09-26
