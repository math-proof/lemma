from util import *


@apply
def apply(eq_r_abs, eq_r_vec, eq_v_vec, eq_v_abs, eq_v_hat, eq_theta):
    r_vec, r_abs = eq_r_abs.of(Equal[Norm])
    (r_hat, S[r_abs]), S[r_vec] = eq_r_vec.of(Equal[Mul])

    (S[r_vec], (t, S[1])), v_vec = eq_v_vec.of(Equal[Derivative])
    S[v_vec], v_abs = eq_v_abs.of(Equal[Norm])
    (v_hat, S[v_abs]), S[v_vec] = eq_v_hat.of(Equal[Mul])

    ((S[r_vec], (S[t], S[1])), (θ, (S[t], S[1]))), θ_hat = eq_theta.of(Equal[Derivative / Derivative])
    return Equal(v_vec, r_hat * Derivative[t](r_abs) + r_abs * Derivative[t](r_hat))


@prove
def prove(Eq):
    from Lemma import Calculus

    t = Symbol(real=True)
    r_vec = Function(r"\vec{r}", shape=(2,), real=True)
    r_hat = Function(r"\hat{r}", shape=(2,), real=True)
    r_abs = Function("r", shape=(), real=True)
    v_vec = Function(r"\vec{v}", shape=(2,), real=True)
    v_hat = Function(r"\hat{v}", shape=(2,), real=True)
    v_abs = Function("v", shape=(), real=True)

    θ_hat = Function(r"\hat{\theta}", shape=(2,), real=True)
    θ = Function(shape=(), real=True)
    Eq << apply(
        Equal(r_abs(t), Norm(r_vec(t))),
        Equal(r_vec(t), r_abs(t) * r_hat(t)),
        Equal(v_vec(t), Derivative[t](r_vec(t))),
        Equal(v_abs(t), Norm(v_vec(t))),
        Equal(v_vec(t), v_abs(t) * v_hat(t)),
        Equal(θ_hat(t), Derivative[t](r_vec(t)) /  Derivative[t](θ(t))),
        )

    Eq << Eq[2].subs(Eq[1])

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.Mul.eq.Add)




if __name__ == '__main__':
    run()
# created on 2022-01-19
