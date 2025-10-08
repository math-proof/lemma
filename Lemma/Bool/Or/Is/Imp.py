from util import *



def ou_to_sufficient(self, index):
    eqs = [*self.args]
    p = eqs[index]
    if isinstance(index, slice):
        p = Or(*p)

    del eqs[index]
    q = Or(*eqs).simplify()
    return Imply(p.invert(), q)


@apply
def apply(self, index):
    [*eqs] = self.of(Or)
    p = eqs[index]
    if isinstance(index, slice):
        p = Or(*p)

    del eqs[index]
    q = Or(*eqs)

    return ou_to_sufficient(self, index).simplify()


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    x, y = Symbol(integer=True)
    B = Symbol(etype=dtype.integer)
    f, g = Function(integer=True)

    Eq << apply(Or(x <= y, f(x) > g(y), Element(y, B)), index=slice(1, 3))

    Eq << Eq[-1].this.rhs.apply(Bool.Imp.Is.Or_Not)


if __name__ == '__main__':
    run()
# created on 2020-02-21
