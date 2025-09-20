from util import *


@apply
def apply(self, *, simplify=True):
    from Lemma.Probability.Sum.Expect.eq.Expect.Sum import rewrite
    return Equal(self, rewrite(Stack, self, simplify))


@prove
def prove(Eq):
    from Lemma import Probability

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    f = Function(real=True)
    x = Symbol(real=True, random=True, shape=(oo,))
    s = Symbol(real=True, random=True)
    Eq << apply(Stack[k:n](Expectation(f(x[k]) | s)), simplify=False)

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.Stack.eq.Stack.Expect)




if __name__ == '__main__':
    run()
# created on 2023-04-02
