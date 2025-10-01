from util import *


@apply
def apply(imply):
    lhs, rhs = imply.of(Equal)
    return Equal(exp(lhs), exp(rhs))

@prove
def prove(Eq):
    from Lemma import Logic

    x = Symbol(real=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(Equal(f(x), g(x)))

    Eq << Eq[1].apply(Logic.EqUfnS.of.Eq, log)


if __name__ == '__main__':
    run()
# created on 2018-08-05
