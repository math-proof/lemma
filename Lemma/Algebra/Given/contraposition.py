from util import *


@apply
def apply(self):
    q, p = self.of(Given)
    return Given(p.invert(), q.invert())


@prove
def prove(Eq):
    from Lemma import Algebra

    p, q = Symbol(bool=True)
    Eq << apply(Given(p, q))

    Eq << Eq[0].this.lhs.apply(Algebra.Given.Is.Or)

    Eq << Eq[-1].this.rhs.apply(Algebra.Given.Is.Or)




if __name__ == '__main__':
    run()
# created on 2019-03-02
# updated on 2022-01-27
