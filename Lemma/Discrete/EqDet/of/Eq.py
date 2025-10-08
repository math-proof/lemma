from util import *


@apply
def apply(given, *, simplify=True):
    lhs, rhs = given.of(Equal)
    if simplify:
        lhs = det(lhs)
        rhs = det(rhs)
    else:
        lhs = Determinant(lhs, evaluate=False)
        rhs = Determinant(rhs, evaluate=False)

    return Equal(lhs, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n, m = Symbol(integer=True, positive=True, given=True)
    i = Symbol(domain=Range(n))
    f, g = Function(shape=(m, m), integer=True)
    Eq << apply(Equal(f(i), g(i)))

    Eq << Bool.EqUFnS.of.Eq.apply(Eq[0], det)




if __name__ == '__main__':
    run()

# created on 2020-02-10
# updated on 2023-03-18
