from util import *


def rewrite(Sum, self):
    [*args], *limits = self.of(Sum[Mul])
    for i, cond in enumerate(args):
        if cond.is_Probability:
            cond = cond.of(Pr)
            break
    else:
        return

    del args[i]

    fx = Mul(*args)

    if isinstance(cond, tuple):
        cond, *weights = cond
    else:
        weights = ()

    if cond.is_Conditioned:
        cond, given = cond.args
    else:
        given = None

    if cond.is_And:
        cond = cond.args
    else:
        cond = [cond]

    for cond in cond:
        x, x_var = cond.of(Equal)
        assert x.is_random
        _fx = fx._subs(x_var, x)
        assert _fx != fx
        fx = _fx

    return Expectation(fx, *weights, given=given)

@apply
def apply(self):
    return Equal(self, rewrite(Sum, self))


@prove
def prove(Eq):
    from Lemma import Probability

    n = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(n, n))
    f = Function(real=True)
    x, s = Symbol(integer=True, random=True)
    Eq << apply(Sum[x.var](Pr[x:θ](x | s) * f(x.var)))

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.eq.Sum)




if __name__ == '__main__':
    run()
# created on 2023-04-02
