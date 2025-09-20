from util import *




@apply
def apply(imply, wrt=None):
    cond = imply.domain_defined(wrt)
    return Or(imply, NotElement(wrt, cond))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True, given=True)
    x = Symbol(shape=(n,), real=True, given=True)
    Eq << apply(x[i] > 0, wrt=i)

    Eq << Logic.All.of.All_OrNot.apply(Eq[1], pivot=1)




if __name__ == '__main__':
    run()

# created on 2019-03-16
# updated on 2023-05-20
