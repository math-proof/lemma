from util import *


@apply
def apply(all_x, all_p, equality):

    (x_cup_finiteset, e), (x, s) = all_x.of(All[Equal])
    (((S[x], (p, k)), (S[k], S[0], n)), S[s]), (S[x], S[s]), (S[p], P) = all_p.of(All[Element[Stack[Indexed[Indexed]]]])

    assert x_cup_finiteset == x.cup_finiteset()
    S[n] = x.shape[0]

    if P.is_set:
        P = P.condition_set().condition

    S[n] = p.shape[0]

    S[p.cup_finiteset()], S[Range(n)] = P.args

    S[e], S[n] = equality.of(Equal[Card])

    return Equal(Card(s), factorial(n))


@prove(proved=False)
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    n = Symbol(domain=Range(2, oo))
    S = Symbol(etype=dtype.integer[n])
    x = Symbol(**S.element_symbol().type.dict)
    i, j, k = Symbol(integer=True)
    e = Symbol(etype=dtype.integer, given=True)
    p = Symbol(shape=(n,), integer=True, nonnegative=True)
    P = Symbol(conditionset(p[:n], Equal(p[:n].cup_finiteset(), Range(n))))
    Eq << apply(All[x:S](Equal(x.cup_finiteset(), e)),
                All[x:S, p[:n]:P](Element(Stack[k:n](x[p[k]]), S)),
                Equal(Card(e), n))

    Eq << Set.Any.Eq.of.Eq_Card.apply(Eq[2])

    Eq << Algebra.Any.All.And.of.All.Any.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(Logic.Eq.of.Eq.Eq)

    a, cond = Eq[-1].limits[0]
    from Lemma.Discrete.And.of.Eq.index import index_function
    index = index_function(n)
    # p= Stack[j:n](index[j](x, a))
    # x[index[j](x, a)] = a[j]
    Eq << Any[a:cond](All[p:P](Element(Stack[k:n](a[p[k]]), S)))

    Eq << Any[a:cond](All[p:P](Equal(p, Stack[j:n](index[j](Stack[k:n](a[p[k]]), a)))))

    Eq << Any[a:cond](All[x:S](Element(Stack[j:n](index[j](x, a)), P)))

    Eq << Any[a:cond](All[x:S](Equal(x, Stack[k:n](a[Stack[j:n](index[j](x, a))[k]]))))


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-09-11
