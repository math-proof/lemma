from util import *



@apply
def apply(self):
    lhs, rhs = self.of(KL[Pr[Equal], Pr[Equal]])
    if lhs[-1].is_Tuple:
        (x, x_var), *limits_lhs = lhs
    else:
        x, x_var = lhs
        limits_lhs = []
        
    if rhs[-1].is_Tuple:
        (x_quote, S[x_var]), *limits_rhs = rhs
    else:
        x_quote, S[x_var] = rhs
        limits_rhs = []
    
    if limits_lhs:
        limit_lhs, = limits_lhs
        if len(limit_lhs) == 1:
            limits = [(x,), *limits_lhs]
        else:
            limits = [(x, *limit_lhs[1:])]
    else:
        limits = [(x,)]         
    return Equal(self, Expectation(log(Pr(Equal(x, x.surrogate), *limits_lhs) / Pr(Equal(x_quote, x.surrogate), *limits_rhs)), *limits))


@prove(provable=False)
def prove(Eq):
    D = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True)
    Eq << apply(KL(Pr[θ](Equal(x, x.var)), Pr[θ_quote](Equal(x, x.var))))

    


if __name__ == '__main__':
    run()
# created on 2021-03-25
# updated on 2023-03-25
