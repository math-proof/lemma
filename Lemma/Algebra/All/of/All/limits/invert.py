from util import *



@apply
def apply(given):
    expr, (x, *cond) = given.of(All)
    return All[x:expr.invert()](given.limits_cond.invert().simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    e = Symbol(real=True)
    f, g = Function(integer=True)

    Eq << apply(All[e:g(e) > 0](f(e) > 0))

    Eq << Bool.Or_Not.of.All.apply(Eq[0])

    Eq << Bool.All.of.All_OrNot.apply(Eq[-1], pivot=0, wrt=e)


if __name__ == '__main__':
    run()

# created on 2018-12-15
