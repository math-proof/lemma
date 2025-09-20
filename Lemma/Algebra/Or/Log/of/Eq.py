from util import *



@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    return Or(Equal(log(lhs), log(rhs)), Equal(lhs, 0))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    b, a = Symbol(real=True)
    x = Symbol(domain=Interval(a, b))
    f, g = Function(real=True)

    Eq << apply(Equal(f(x), g(x)))

    Eq << Eq[1].subs(Eq[0])

    Eq << Logic.Or_And.given.AndOrS.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[0].reversed)

    # the following codes will issue an error because of illegal domain definition
#     Eq << Algebra.eq.then.eq.invoke.apply(Eq[0], log)


if __name__ == '__main__':
    run()

# created on 2019-04-16
