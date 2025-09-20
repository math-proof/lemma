from util import *



@apply
def apply(given):
    x, fx = given.of(Equal)
    if not x.is_Symbol:
        x, fx = fx, x

    assert x.is_given is None
    return Element(x, conditionset(x, given))


@prove
def prove(Eq):
    x = Symbol(integer=True)
    f = Function(complex=True)

    Eq << apply(Equal(f(x), x))

    Eq << Eq[-1].this.rhs.rhs.simplify()

if __name__ == '__main__':
    run()

# created on 2019-09-13
