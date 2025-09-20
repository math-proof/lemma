from util import *


@apply
def apply(given):
    (x, (S[x], expr)), A = given.of(Equal[Cup[FiniteSet]])
    return All[x:A](expr)


@prove
def prove(Eq):
    x = Symbol(integer=True)
    A = Symbol(etype=dtype.integer)
    f = Function(integer=True)
    Eq << apply(Equal(conditionset(x, f(x) > 0), A))

    Eq << Eq[-1].subs(Eq[0].reversed)




if __name__ == '__main__':
    run()

# created on 2020-12-26
# updated on 2023-11-14
