from util import *


@apply(simplify=False)
def apply(given):
    cond, fy = given.of(boolalg.Imply)
    return boolalg.Imply(cond, cond & fy)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    a, c = Symbol(integer=True)
    Eq << apply(boolalg.Imply(Equal(a, 0), Equal(c, 0)))

    Eq << Bool.Imp_And.given.Imp.Imp.apply(Eq[1])



if __name__ == '__main__':
    run()
# created on 2023-05-03



from . import domain_defined
