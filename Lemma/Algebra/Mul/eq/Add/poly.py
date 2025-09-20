from util import *


# return a combination of k elements selected among {0, 1, 2, n - 2, n - 1};
def generate_combination(n, k):
    assert n >= k and k > 0, "n >= k && k > 0"
    x = [0] * k
    i = 0
    while True:
        if x[i] <= n - (k - i):
            if i == k - 1:
                yield [*x]
            else:
                i += 1
                x[i] = x[i - 1]
            x[i] += 1
        else:
            i -= 1
            x[i] += 1  # backtracking to the previous index.
        if x[0] > n - k:
            break


def sigmar(x, k):
    import functools
    if k == 0:
        return 1
    if k == 1:
        return functools.reduce(lambda x, y: x + y, x)
    sigmar = 0
    for indices in generate_combination(len(x), k):
        sigmar += functools.reduce(lambda x, y: x * y, (x[i] for i in indices))
    return sigmar


@apply
def apply(self, x):
    f = self.of(Mul)
    n = len(f)
    y = []
    for f in f:
        S[1], t = f.as_poly(x).all_coeffs()
        t = -t
        y.append(t)

    f = 0
    for k in range(0, n + 1):
        f += sigmar(y, k) * x ** (n - k) * (-1) ** k

    return Equal(self, f)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(complex=True, given=True)
    n = 4
    t = Symbol(complex=True, shape=(n,))
    s = 1
    for i in range(0, n):
        s *= x - t[i]
    Eq << apply(s, x)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS, deep=True)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS, deep=True)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS, deep=True)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS, deep=True)


if __name__ == '__main__':
    run()
# created on 2018-11-15
