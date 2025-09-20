from util import *


def negate(i, *ab):
    if len(ab) == 2:
        a, b = ab
        if i.is_integer:
            return (i, 1 - b, 1 - a)
        else:
            return (i, -b, -a)
    elif len(ab) == 1:
        domain, = ab
        return (i, -domain)
    else:
        return (i,)

@apply
def apply(self):
    expr, (i, *ab) = self.of(All)
    return All(expr._subs(i, -i), negate(i, *ab))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    i, a, b = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(All[i:a:b](f(i) >= 0))

    Eq << Logic.Or_Not.of.All.apply(Eq[0])

    Eq << Eq[-1].subs(i, -i)

    Eq << Eq[-1].this.find(NotElement).apply(Set.NotIn.Neg.of.NotIn)

    Eq << Logic.All.given.All_Or_Not.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2018-12-08
# updated on 2023-05-20
