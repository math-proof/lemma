from util import *



@apply
def apply(given, d):
    lhs, rhs = given.of(Equal)
    return Equal(lhs / d, rhs / d) | Equal(d, 0)


@prove
def prove(Eq):
    from Lemma import Algebra
    b, a = Symbol(real=True)
    x = Symbol(domain=Interval(a, b), given=True)
    f, g = Function(real=True)
    d = Symbol(real=True, given=True)

    Eq << apply(Equal(f(x), g(x)), d)

    Eq << ~Eq[1]

    Eq << Eq[-1].apply(Algebra.NeMul.of.Ne_0.Ne)

    Eq <<= Eq[0] & Eq[-1]

if __name__ == '__main__':
    run()

# created on 2019-04-16
