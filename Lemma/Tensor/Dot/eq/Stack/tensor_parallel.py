from util import *


@apply
def apply(self, t_p):
    s, W = self.of(Expr @ Expr)
    W = W.T
    W = W.split(W.shape[0] / t_p, dim=0)
    i = s.generate_var(integer=True, excludes=W.variables_set | W.free_symbols, domain=Range(t_p))

    return Equal(self, Transpose[0, 2](Stack[i:t_p](s @ W[i].T)).reshape(*self.shape))

@prove
def prove(Eq):
    from Lemma import Algebra

    # m denotes batch size
    # n denotes sequence length
    # d denotes hidden size
    # d_o denotes output hidden size
    # t_p denotes tensor parallel
    m, n, d, d_o, t_p = Symbol(integer=True, positive=True)
    d_o *= t_p
    # s denotes hidden states
    s = Symbol(real=True, shape=(m, n, d))
    W = Symbol(real=True, shape=(d_o, d))
    Eq << apply(s @ W.T, t_p)


    Eq << Eq[-1].this.find(Mod).apply(Algebra.Mod.eq.Sub_Mul_Div)





    # https://github.com/huggingface/transformers/blob/main/src/transformers/models/llama/modeling_llama.py#L369



if __name__ == '__main__':
    run()
# created on 2023-12-25
# updated on 2023-12-26
