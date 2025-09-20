from util import *


@apply
def apply(eq_sum, eq_union, x=None):
    w_sum, M = eq_sum.of(Equal)
    w_union, M_Interval = eq_union.of(Equal)

    S[0], S[M] = M_Interval.of(Range)

    wi, i = w_sum.of(Sum[Card, Tuple])
    S[wi], S[i] = w_union.of(Cup[Tuple])

    w, S[i] = wi.of(Indexed)

    assert x.shape[0] == M

    w_ = Symbol("omega^'", cluster(w, x))

    return Equal(Sum[i](Card(w_[i])), M), Equal(Cup[i](w_[i]), M_Interval)


def mean(wi, x):
    j = Symbol(integer=True)
    return Sum[j:wi](x[j]) / Card(wi)


def __getitem__(self, indices):
    if isinstance(indices, (tuple, list)):
        return Indexed(self, *indices)
    return Indexed(self, indices)


mean = Function(shape=property(lambda self: self.args[1].shape[1:]), real=True, eval=mean, __getitem__=__getitem__)


# c is a list of vectors, (k, n)
# return a list of set of integers, (k,)
def cluster(w, x):
    i, j = Symbol(integer=True)
    k = w.shape[0]
    return Stack[i:k](conditionset(j, Equal(ArgMin[i](Norm(x[j] - mean(w[i], x))), i)))


cluster = Function(eval=cluster, __getitem__=__getitem__)


@prove
def prove(Eq):
    from Lemma import Set

    M, n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    k = Symbol(domain=Range(M))
    x = Symbol(real=True, shape=(M, n))
    w = Symbol(shape=(k,), etype=dtype.integer, empty=False)
    Eq << apply(Equal(Sum[i](Card(w[i])), M), Equal(Cup[i](w[i]), k.domain), x=x)

    Eq << Eq[2].this.rhs.defun()

    Eq.omega_i_definition0 = Eq[-1][i]

    Eq.omega_i_definition = Eq.omega_i_definition0.this.rhs.apply(Set.Conditionset.rewrite.domain_defined)

    j = Eq.omega_i_definition.rhs.variable
    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[4], wrt=j)

    Eq <<= Eq[-2].this.lhs.apply(Set.Any_In.of.In_Cup), \
    Eq[-1].this.rhs.apply(Set.In_Cup.given.Any_In)

    Eq <<= Eq[-2].subs(Eq.omega_i_definition), Eq[-1].subs(Eq.omega_i_definition0)

    Eq << Eq[-2].this.lhs.expr.simplify()

    Eq << Eq[-1].this.rhs.expr.simplify()

    w_ = Eq.omega_i_definition.lhs.base
    k_ = Symbol(integer=True)
    Eq.nonoverlapping = All[i:k_](Equal(w_[i] & w_[k_], w_[i].etype.emptySet), plausible=True)

    Eq << Eq.omega_i_definition0.subs(i, k_)

    Eq << Set.EqInter.of.Eq.Eq.apply(Eq.omega_i_definition0, Eq[-1])

    Eq << Eq[-1].this.find(And).apply(Set.In.Finset.of.Eq.Eq)

    Eq << Eq.nonoverlapping.subs(Eq[-1])

    Eq << Eq[-1].this().find(Intersection).simplify()

    Eq << Set.Eq.of.All_Eq_Empty.nonoverlapping.intlimit.utility.apply(Eq.nonoverlapping, k)

    Eq << Eq[-1].this.find(Cup).limits_subs(k_, i)

    Eq << Eq[-1].this.rhs.limits_subs(k_, i)

    Eq << Eq[-1].subs(Eq[4]).reversed


if __name__ == '__main__':
    run()
# created on 2020-12-24
