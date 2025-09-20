from util import *


@apply
def apply(self):
    args = self.of(Im[Add])
    args = [Im(arg) for arg in args]
    return Equal(self, Add(*args))


@prove
def prove(Eq):
    from Lemma import Algebra

    z, w = Symbol(complex=True)
    Eq << apply(Im(z + w, evaluate=False))

    Eq << Eq[0].this.rhs.apply(Algebra.Add.eq.Im)




if __name__ == '__main__':
    run()
# created on 2023-06-03
