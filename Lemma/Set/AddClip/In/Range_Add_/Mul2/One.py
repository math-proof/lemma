from util import *


@apply
def apply(x, k):
    return Element(k + clip(x, -k, k), Range(2 * k + 1))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra

    k = Symbol(integer=True, positive=True)
    x = Symbol(integer=True)
    Eq << apply(x, k)
    
    Eq << Eq[0].this.find(clip).defun()

    
    


if __name__ == '__main__':
    run()
# created on 2021-01-03
# updated on 2022-02-19
