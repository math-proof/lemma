from util import *


def extract(Sum, self):
    expr, *limits = self.of(Expectation)
    if expr.is_Conditioned:
        expr, given = expr.args
    else:
        given = None

    expr, *limits_s = expr.of(Sum)

    subs = []
    for k, *ab in reversed(limits_s):
        if len(ab) == 2 and k.is_integer:
            a, b = ab
            for new, old in subs:
                a = a.subs(old, new)
                b = b.subs(old, new)
            _k = k.copy(domain=Range(a, b))
            expr = expr._subs(k, _k)
            subs.append((_k, k))

    expr = self.func(expr, *limits, given=given)
    for new, old in reversed(subs):
        expr = expr._subs(new, old)

    return Sum(expr, *limits_s)

@apply
def apply(self):

    return Equal(self, extract(Sum, self))


@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Bool

    n = Symbol(integer=True, positive=True, given=False)
    f = Function(real=True)
    s = Symbol(integer=True, random=True)
    x = Symbol(real=True, random=True, shape=(oo,))
    k = Symbol(integer=True)
    Eq << apply(Expectation(Sum[k:n](f(x[k])) | s))



    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.find(Sum).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.eq.Add)

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Bool.Eq_Ite.of.All_Imp.apply(Eq[-1], n, start=1)




if __name__ == '__main__':
    run()
# created on 2023-04-01
