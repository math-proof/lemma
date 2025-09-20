from util import *


def extract(expr, z):
    z_quote = Dummy('z_quote', shape=z.shape, **z.dtype.dict)
    expr = expr._subs(~z, z_quote)

    try:
        coeffs = expr.as_poly(z, z_quote).as_dict()
    except:
        return []

    results = []
    for (i, j), v in coeffs.items():
        std.setitem(results, i, j, v)

    return results

def quadratic_coefficient(self, z=None):
    if z is None:
        for z in self.free_symbols:
            if ~z == z:
                continue

            coeffs = extract(self, z)
            if len(coeffs) == 2:
                if len(coeffs[1]) == 2:
                    return z, coeffs
        else:
            return
    else:
        coeffs = extract(self, z)
        return z, coeffs

@apply
def apply(el, self, z=None):
    a, R = el.of(Element)
    assert not R & {0} and R in Reals
    # coeffs[i, j] is the coefficient of z ** i * (~z) ** j
    z, coeffs = quadratic_coefficient(self, z)

    S[a] = coeffs[1][1]
    b = coeffs[1][0]
    S[~b] = coeffs[0][1]
    c = coeffs[0][0]
    if c is None:
        c = 0
    # assert a.is_real
    rest = c - b * ~b / a
    z += ~b / a
    return Equal(self, a * z * ~z + rest, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    z, a, b, c = Symbol(complex=True)
    Eq << apply(Element(a, Reals - {0}), a * z * ~z + b * z + ~b * ~z + c)

    Eq << Eq[1].this.rhs.expand()

    Eq << Set.EqConj.of.IsReal.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Logic.And_And.given.And.Cond.apply(Eq[-1])

    Eq << Set.Ne_0.of.IsNotZero.apply(Eq[0])

    Eq << Algebra.Conj.ne.Zero.of.Ne_0.apply(Eq[-2])





if __name__ == '__main__':
    run()
# created on 2023-05-02

# updated on 2023-06-25
