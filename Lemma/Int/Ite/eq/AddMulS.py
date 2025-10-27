from util import *


def from_FiniteSet(self, x):
    eq = 1
    for arg in self.args:
        eq *= 1 - KroneckerDelta(x, arg)
    return 1 - eq


def from_Bool(self):
    if self.is_Equal:
        return KroneckerDelta(*self.args)
    if self.is_Unequal:
        return 1 - KroneckerDelta(*self.args)

    if self.is_Greater:
        lhs, rhs = self.args
        if lhs.is_Symbol:
            domain = lhs.domain_assumed
            if domain and (domain.is_Range or domain.is_Interval) and rhs == domain.min():
                return 1 - KroneckerDelta(lhs, rhs)

        if rhs.is_Symbol:
            domain = rhs.domain_assumed
            if domain and (domain.is_Range or domain.is_Interval) and domain.max() == lhs:
                return 1 - KroneckerDelta(lhs, rhs)

        return

    if self.is_Less:
        lhs, rhs = self.args
        if lhs.is_Symbol:
            domain = lhs.domain_assumed
            if domain and domain.is_Range:
                a, b = domain.args
                if not b.is_infinite and b - 1 == rhs:
                    return 1 - KroneckerDelta(lhs, rhs)
                if not a.is_infinite and a == rhs - 1:
                    return KroneckerDelta(lhs, a)
        if rhs.is_Symbol:
            domain = rhs.domain_assumed
            if domain and domain.is_Range:
                if lhs == domain.min():
                    return 1 - KroneckerDelta(lhs, rhs)

        return

    if self.is_And:
        eq = 1
        for c in self.args:
            e = from_Bool(c)
            if e is None:
                return
            eq *= e
        return eq

    if self.is_Or:
        eq = 1
        for c in self.args:
            e = from_Bool(c)
            if e is None:
                return
            eq *= 1 - e
        return 1 - eq

    if self.is_Element:
        x, domain = self.args
        if domain.is_FiniteSet:
            return from_FiniteSet(domain, x)

        domain = x.domain - domain
        if domain.is_FiniteSet:
            return 1 - from_FiniteSet(domain, x)

        return


    if self.is_NotElement:
        x, domain = self.args
        if domain.is_FiniteSet:
            return 1 - from_FiniteSet(domain, x)
        domain = x.domain - domain
        if domain.is_FiniteSet:
            return from_FiniteSet(domain, x)

        return


def from_Expr(self):

    if self.is_Bool:
        delta = from_Bool(self.arg)
        if delta is None:
            return self
        return delta

    if self.is_Piecewise:
        e, c = self.args[0]
        eq = from_Bool(c)
        if eq is None:
            return self

        if len(self.args) == 2:
            rest, _ = self.args[1]
            if rest.is_Piecewise:
                rest = from_Expr(rest)
            elif rest.is_Mul or rest.is_Add:
                args = [*rest.args]
                hit = False
                for i, p in enumerate(args):
                    if p.is_Piecewise:
                        args[i] = from_Expr(p)
                        hit = True
                if hit:
                    rest = rest.func(*args)
        else:
            rest = from_Expr(self.func(*self.args[1:]))
        if e.is_Piecewise or e.is_Add or e.is_Mul:
            e = from_Expr(e)
        return ((e * eq).simplify() + (rest * (1 - eq)).simplify()).simplify()

    if self.is_AssocOp:
        return self.func(*(from_Expr(arg) for arg in self.args))
    return self

@apply
def apply(self):
#     assert self.is_Piecewise
    return Equal(self, from_Expr(self), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n, k = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n))
    x, y = Symbol(real=True, shape=(k,), given=True)
    g, f, h = Function(real=True)
    Eq << apply(Piecewise((g(i), i < n - 1), (h(i), True)))

    Eq << Eq[0].this.lhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite)

    Eq << Eq[-1].this.find(GreaterEqual).apply(Algebra.Ge.Is.Eq.squeeze)


if __name__ == '__main__':
    run()
# created on 2019-10-14
