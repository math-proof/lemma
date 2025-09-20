from util import *


@apply
def apply(is_zero, n=None):
    x = is_zero.of(Equal[Cos, 0])
    if n is None:
        n = is_zero.generate_var(integer=True, var='n')
    assert Integers in n.domain
    return Any[n](Equal(x, S.Pi / 2 + S.Pi * n))


@prove
def prove(Eq):
    from Lemma import Trigonometry, Algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(cos(x), 0))





    Eq << Trigonometry.Eq.of.Cos.eq.Zero.apply(Eq[0])
    Eq << Algebra.Any.given.Cond.subst.apply(Eq[1], Eq[1].variable, Floor(x / S.Pi))

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2018-06-24
