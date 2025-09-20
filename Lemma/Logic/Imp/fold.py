from util import *


@apply
def apply(self, index=0, swap=False):
    [*eqs], q = self.of(Imply[And, Basic])

    r = eqs[index]
    if isinstance(r, list):
        r = And(*r)

    del eqs[index]
    p = And(*eqs)
    if swap:
        r, p = p, r

    return Imply(r, Imply(p, q))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, y, z = Symbol(real=True)
    A, B, C = Symbol(etype=dtype.real)
    Eq << apply(Imply(Element(x, A) & Element(y, B), Element(z, C)), index=0, swap=True)

    Eq << Eq[-1].this.rhs.apply(Logic.Imp.flatten)


if __name__ == '__main__':
    run()
# created on 2019-09-01
