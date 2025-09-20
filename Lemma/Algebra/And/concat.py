from util import *


@apply
def apply(self, i=None, j=None):
    [*eqs] = self.of(And)

    eq_historic = eqs[i]
    eq_n = eqs[j]

    del eqs[i]
    eqs.remove(eq_n)

    lhs, rhs = eq_historic.of(Equal)
    n = lhs.shape[0]

    if lhs.is_Stack and rhs.is_Stack and lhs.variable == rhs.variable:
        k = rhs.variable
    else:
        k = eq_historic.generate_var(integer=True)

    fx = lhs[k]
    gy = rhs[k]

    _lhs, _rhs = eq_n.of(Equal)

    assert fx._subs(k, n) == _lhs
    assert gy._subs(k, n) == _rhs

    rhs = And(*eqs, Equal(Stack[k:n + 1](fx).simplify(), Stack[k:n + 1](gy).simplify()))
    return rhs


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    f, g = Function(real=True)
    x = Symbol(real=True)
    A = Symbol(etype=dtype.real)
    Eq << apply(Equal(Stack[k:n](f(k)), Stack[k:n](g(k))) & Equal(f(n), g(n)) & Element(x, A), i=1, j=0)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq <<= Logic.Imp_And.given.Imp.delete.apply(Eq[-2]), Eq[-1].this.lhs.args[0].apply(Algebra.And.Eq.of.Eq.split, simplify=None)

    Eq << Eq[-1].this.lhs.apply(Algebra.Eq.of.Eq.Eq.concat, simplify=None)




if __name__ == '__main__':
    run()
# created on 2019-05-01
# updated on 2023-03-26
