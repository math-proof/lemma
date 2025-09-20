from util import *


@apply
def apply(x):
    return relu(x) >= x


@prove
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(x)

    Eq << Eq[0].this.lhs.defun()





if __name__ == '__main__':
    run()
# created on 2021-12-18
