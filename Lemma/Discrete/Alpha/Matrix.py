from util import *


@apply
def apply(A):
    from Lemma.Discrete.Alpha.gt.Zero import alpha

    mat = A.of(alpha)

    return Equal(A, alpha(*mat.of(Matrix)))


@prove
def prove(Eq):
    from Lemma.Discrete.Alpha.gt.Zero import alpha
    x = Symbol(real=True, positive=True, shape=(oo,))
    Eq << apply(alpha(Matrix((x[0], x[1], x[2]))))

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

if __name__ == '__main__':
    run()


# created on 2020-09-26
