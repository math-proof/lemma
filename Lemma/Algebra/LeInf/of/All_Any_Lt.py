from util import *


@apply
def apply(given):
    ((fx, M), *limits), (S[M], M0, S[oo]) = given.of(All[Any[Less]])
    return Inf(fx, *limits) <= M0


@prove
def prove(Eq):
    from Lemma import Algebra

    M0, a, b = Symbol(real=True, given=True)
    M, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[M:M0:oo](Any[x:Interval(a, b)](f(x) < M)))

    Eq << ~Eq[1]

    Eq << Algebra.Any.All.Ge.of.GtInf.apply(Eq[-1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-01-05
