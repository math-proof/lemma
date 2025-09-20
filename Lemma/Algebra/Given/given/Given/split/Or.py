from util import *



@apply
def apply(given):
    fx, ou = given.of(Given)
    eqs = ou.of(Or)
    return tuple(Given(fx, eq) for eq in eqs)


@prove
def prove(Eq):
    from Lemma import Algebra
    x, b, a = Symbol(integer=True)
    f, g = Function(integer=True)


    Eq << apply(Given(f(x) > g(x), (a > b) | (f(a) > f(b))))

    Eq << Algebra.Given.Or.of.Given.Given.apply(Eq[1], Eq[2])

if __name__ == '__main__':
    run()
# created on 2019-03-03
