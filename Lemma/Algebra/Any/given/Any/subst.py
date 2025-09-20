from util import *


@apply
def apply(self, old, new):
    from sympy.concrete.limits import limits_intersect
    assert not old.is_given
    exists = self.limits_dict
    if old in exists:
        domain = exists[old]
        if not domain:
            domain = old.domain
        eqs = []

        if not isinstance(domain, list):
            if not domain.is_set:
                domain = old.domain_conditioned(domain)
            if new.is_symbol:
                domain_defined = self.expr.domain_defined(new)
                if domain_defined not in domain:
                    eqs.append(Element(new, domain))
            else:
                eqs.append(Element(new, domain))

        if self.expr.is_And:
            for equation in self.expr.args:
                eqs.append(equation.subs(old, new))
        else:
            eqs.append(self.expr._subs(old, new))
        limits = self.limits_delete(old)
        if new.is_symbol and new.definition is None and not new.is_given:
            limits = limits_intersect(limits, [(new,)])

        vars = {x for x, *_ in limits}
        limits += [(s,) for s in new.free_symbols if not s.is_given and s not in vars]

        assert limits
        return self.func(And(*eqs), *limits)

    if old.is_Sliced:
        from Lemma.Algebra.Slice.eq.Matrix import convert
        old = convert(old)
        if old.is_DenseMatrix:
            old = Tuple(*old._args)
            if old in exists or all(sym in exists for sym in old):
                ...
            else:
                return

    if old.is_Tuple and all(sym in exists for sym in old):
        domains = [exists[sym] for sym in old]
        eqs = []

        for domain in domains:
            if not isinstance(domain, list):
                if not domain.is_set:
                    domain = old.domain_conditioned(domain)
                eqs.append(Element(new, domain))

        if self.expr.is_And:
            for equation in self.expr.args:
                eqs.append(equation._subs(old, new))
        else:
            if old.is_Tuple:
                function = self.expr
                for i in range(len(old)):
                    function = function._subs(old[i], new[i])
                eqs.append(function)
            else:
                eqs.append(self.expr._subs(old, new))
        limits = self.limits_delete(old)
        if new.is_symbol:
            limits = limits_intersect(limits, [(new,)])

        assert limits
        return self.func(And(*eqs), *limits)

@prove
def prove(Eq):
    e = Symbol(real=True)
    x = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Any[x](x > g(x)), x, f(e))

    Eq << ~Eq[0]

    Eq << Eq[-1].simplify()

    Eq << Eq[-1].subs(x, f(e))

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()

# created on 2019-02-16
