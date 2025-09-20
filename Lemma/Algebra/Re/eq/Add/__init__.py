from util import *


@apply
def apply(self):
    args = self.of(Re[Add])
    args = [Re(arg) for arg in args]
    return Equal(self, Add(*args))


@prove
def prove(Eq):
    from Lemma import Algebra

    z, w = Symbol(complex=True)
    Eq << apply(Re(z + w, evaluate=False))

    Eq << Eq[0].this.rhs.apply(Algebra.Add.eq.Re)


if __name__ == '__main__':
    run()
# created on 2023-06-03

from . import Conj
