from util import *


def rewrite(Sum, self):
    from _collections import defaultdict
    [*args], *limits = self.of(Sum[Mul])

    for i, b in enumerate(args):
        if b.is_Bool:
            break
    else:
        return

    del args[i]
    function = Mul(*args)

    cond = b.arg
    variables = self.variables
    variables_set = {*variables}
    if cond.is_And:
        eqs = {*cond.args}
        dic = defaultdict(set)
        for v in variables:
            otherVars = variables_set - {v}
            for eq in eqs:
                if eq._has(v) and not eq.has(*otherVars):
                    dic[v].add(eq)
            eqs -= dic[v]

        if eqs:
            for eq in eqs:
                for v, s in dic.items():
                    if not s and eq._has(v):
                        dic[v].add(eq)
                        break
                else:
                    return

        for v, cond in self.limits_dict.items():
            if not cond:
                continue
            if cond.is_set:
                cond = Element(v, cond)
            dic[v].add(cond)

        graph = {x: set() for x in variables_set}
        for y, eqs in dic.items():
            if not eqs:
                continue

            free_symbols = set.union(*(eq.free_symbols for eq in eqs)) & (variables_set - {y})
            for x in free_symbols:
                # y is dependent on x, so x is a parent of y
                graph[x].add(y)

        from sympy.utilities.iterables import topological_sort_depth_first
        G = topological_sort_depth_first(graph)
        # print(G)

        limits = []
        for v in G:
            eqs = dic[v]
            domain = None

            for el in eqs:
                if el.is_Element and el.lhs == v:
                    domain = el.rhs
                    eqs.remove(el)
                    break

            if eqs:
                cond = And(*eqs)
                if domain is None:
                    limit = (v, cond)
                else:
                    limit = (v, cond, domain)
            else:
                limit = (v, domain)

            limits.append(limit)

    else:
        for i, v in enumerate(variables):
            if cond._has(v):
                v, *ab = limits[i]
                if ab:
                    domain = v.range(*ab)
                else:
                    domain = v.universalSet

                if cond.is_Element and cond.lhs == v:
                    cond = cond.rhs
                    cond &= domain

                limits[i] = (v, cond)
                break

    return Sum(function, *limits)

@apply
def apply(self):
    return Equal(self, rewrite(Sum, self), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Finset

    A, C = Symbol(etype=dtype.integer)
    B = Function(etype=dtype.integer)
    x, y, z = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[x, y, z:C](f(x, y) * functions.Bool(Element(x, A) & Element(y, B(x)))))

    Eq << Eq[0].this.rhs.apply(Finset.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.lhs.apply(Finset.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.rhs.find(functions.Bool).apply(Bool.BoolAnd.eq.MulBoolS)

    Eq << Eq[-1].this.lhs.find(functions.Bool[And]).apply(Bool.BoolAnd.eq.MulBoolS)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.swap)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.swap, 1, 2)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.swap)





if __name__ == '__main__':
    run()
# created on 2018-05-01
# updated on 2023-06-18
