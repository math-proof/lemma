from util import *


@apply(simplify=False)
def apply(eq_conj, self, z=None):
    b_quote, b_bar = eq_conj.of(Equal)
    b = ~b_bar
    from Lemma.Set.EqConj.of.IsNotZero.square_completing import quadratic_coefficient
    z, coeffs = quadratic_coefficient(self, z)

    a = coeffs[1][1]
    try:
        S[b] = coeffs[1][0]
        S[b_quote] = coeffs[0][1]
    except Exception as e:
        print('try to prove:')
        print('Equal(%s, %s, plausible=True)' % (coeffs[0][1], ~coeffs[1][0]))
        raise e

    assert a.is_nonzero and a.is_real
    c = coeffs[0][0]

    rest = c - b * ~b / a
    z += ~b / a
    return Equal(self, a * z * ~z + rest, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Set

    z, a, b, b_quote, c = Symbol(complex=True)
    a = Symbol(real=True, zero=False)
    Eq << apply(Equal(b_quote, ~b), a * z * ~z + b * z + b_quote * ~z + c)

    Eq << Unequal(a, 0, plausible=True)

    Eq << Element(a, Reals, plausible=True)

    Eq << Set.In.Union.of.Ne_0.IsReal.apply(Eq[-2], Eq[-1])

    Eq << Set.EqConj.of.IsNotZero.square_completing.apply(Eq[-1], Eq[1].lhs._subs(b_quote, ~b), simplify=None)

    Eq << Eq[1].subs(Eq[0])




if __name__ == '__main__':
    run()
# created on 2023-05-02
