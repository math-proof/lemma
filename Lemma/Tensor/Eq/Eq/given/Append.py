from util import *


@apply
def apply(given, index=-1):
    lhs, rhs = given.of(Equal[Matrix, Matrix])

    first = Equal(Matrix(lhs[:index]), Matrix(rhs[:index])).simplify()
    second = Equal(Matrix(lhs[index:]), Matrix(rhs[index:])).simplify()

    return first, second


@prove
def prove(Eq):
    a, b, c, d = Symbol(real=True)
    Eq << apply(Equal(Matrix([a, b]), Matrix([c, d])))

    Eq << Eq[0].this.lhs.subs(Eq[-2]).subs(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-08-28
