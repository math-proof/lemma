from util import *


@apply
def apply(eq_R, i_, j_, clustered=False):
    if clustered:
        (cosi, sini, S[0], S[0], \
            S[-sini], S[cosi], S[0], S[0], \
            S[0], S[0], cosj, sinj, \
            S[0], S[0], S[-sinj], S[cosj]), R = eq_R.of(Equal[Matrix])
    else:
        (cosi, S[0], sini, S[0], \
            S[0], cosj, S[0], sinj, \
            S[-sini], S[0], S[cosi], S[0], \
            S[0], S[-sinj], S[0], S[cosj]), R = eq_R.of(Equal[Matrix])
    sini = -sini
    sinj = -sinj
    i = sini.of(Sin)
    j = sinj.of(Sin)
    S[i] = cosi.of(Cos)
    S[j] = cosj.of(Cos)
    R, S[i], S[j] = R.of(Indexed)
    return Equal(R[i_, j_].T @ R[i, j],R[i - i_, j - j_])

def rotary_matrix(i, j, clustered=False):
    if clustered:
        return [
            [cos(i), -sin(i),      0,       0],
            [sin(i),  cos(i),      0,       0],
            [     0,       0, cos(j), -sin(j)],
            [     0,       0, sin(j),  cos(j)]]
    else:
        return [
            [cos(i),      0, -sin(i),       0],
            [     0,  cos(j),      0, -sin(j)],
            [sin(i),       0, cos(i),       0],
            [     0,  sin(j),      0,  cos(j)]]
@prove
def prove(Eq):
    from Lemma import Trigonometry, Algebra, Logic

    # n denotes sequence length (seq_length)
    n = Symbol(integer=True, positive=True)
    # R denotes rotary matrix
    R = Symbol(shape=(n, n, 4, 4), real=True)
    i, j, i_quote, j_quote = Symbol(integer=True)
    Eq << apply(Equal(R[i, j], rotary_matrix(i, j)), i_quote, j_quote)

    Eq << Eq[0].subs(i, i_quote).subs(j, j_quote).T @ Eq[0]

    Eq <<= Eq[-1].rhs.find(Sin * Sin + Cos * Cos).this.apply(Trigonometry.Add.eq.Cos),\
        Eq[-1].rhs.find(Sin * Cos - Sin * Cos).this.apply(Trigonometry.Sub.eq.Sin)

    Eq << -Eq[-1]

    Eq << Eq[-1].find(-~Sin).this.apply(Trigonometry.Sin.eq.Neg.Sin)

    Eq << Eq[-5].subs(*Eq[-4:])

    Eq <<= Eq[-1].rhs.find(Sin * Sin + Cos * Cos).this.apply(Trigonometry.Add.eq.Cos),\
        Eq[-1].rhs.find(Sin * Cos - Sin * Cos).this.apply(Trigonometry.Sub.eq.Sin)

    Eq << -Eq[-1]

    Eq << Eq[-1].find(-~Sin).this.apply(Trigonometry.Sin.eq.Neg.Sin)

    Eq << Eq[-5].subs(*Eq[-4:])

    Eq << Eq[0].subs(i, i - i_quote).subs(j, j - j_quote)

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[-2], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-09-16

# updated on 2023-09-17
