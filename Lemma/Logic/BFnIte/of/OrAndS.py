from util import *


def expr_cond_pair(cls, or_eqs, wrt, reverse=None):
    expr = []
    cond = []
    for eq in or_eqs:
        [*and_eqs] = eq.of(And)

        for i, eq in enumerate(and_eqs):
            if isinstance(eq, cls):
                if wrt == eq.rhs:
                    expr.append(eq.lhs)
                    break
                elif reverse and wrt == eq.lhs:
                    expr.append(eq.rhs)
                    break

        assert eq is and_eqs[i]
        assert isinstance(eq, cls)
        del and_eqs[i]
        condition = And(*and_eqs)

        for c in cond:
            # if not (condition & c).is_BooleanFalse:
                # print(condition & c)
            assert (condition & c).is_BooleanFalse, "%s is not false!" % str(condition & c)

        cond.append(condition)
    ec = [[e, c] for e, c in zip(expr, cond)]
    ec[-1][1] = True
    return ec


@apply
def apply(given, wrt=None):
    or_eqs = given.of(Or)

    assert len(or_eqs) == 2
    return Element(Piecewise(*expr_cond_pair(Element, or_eqs, wrt)).simplify(), wrt)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,), given=True)
    A, S = Symbol(etype=dtype.real[k], given=True)
    f, g = Function(shape=(k,), real=True)
    Eq << apply(Element(f(x), S) & Element(x, A) | Element(g(x), S) & NotElement(x, A), wrt=S)

    Eq << Eq[1].apply(Logic.Cond.given.Or.OrNot, cond=Element(x, A))

    Eq << Logic.And_And.given.And.Cond.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].apply(Logic.BFn.of.BFnIte.Cond, invert=True, ret=0), Eq[-1].apply(Logic.BFn.of.BFnIte.Cond, ret=0)

    Eq <<= Eq[-2] & Eq[0], Eq[-1] & Eq[0]

    Eq << Logic.OrAndS.of.And_Or.apply(Eq[-1])

    Eq << Logic.OrAndS.of.And_Or.apply(Eq[-2])





if __name__ == '__main__':
    run()

# created on 2018-03-07
# updated on 2023-05-14
