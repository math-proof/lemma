from util import *


@apply
def apply(self):
    fx, (x, S) = self.of(Sum)
    A, B = S.of(Complement)
    return Equal(self, Sum[x:A](fx) - Sum[x:A & B](fx), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(integer=True)
    f = Function(real=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Sum[x:A - B](f(x)))

    Eq << Eq[-1].this.rhs.args[0].apply(Algebra.Sum.eq.Add.split, cond=B)














if __name__ == '__main__':
    run()
# created on 2020-03-23
