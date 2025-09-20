from util import *


@apply
def apply(given):
    (lt, (x, *ab)), [delta] = given.of(Any[All])

    if len(ab) == 2:
        domain = x.range(*ab)
    else:
        domain, = ab

    abs_fx_A, epsilon = lt.of(Less)

    assert epsilon.is_symbol
    assert epsilon > 0
    assert epsilon.is_given is None

    fx_A = abs_fx_A.of(Abs)

    if fx_A.is_Add:
        fx, A = std.array_split(fx_A.of(Add), lambda arg: arg._has(x))
        fx = Add(*fx)
        A = -Add(*A)
    else:
        fx = fx_A
        A = 0

    assert delta >= 0

    if x.is_integer:
        assert delta.is_integer

        if domain.is_set:
            N1 = domain.of(Range[Infinity])
            S[delta] = N1 - 1
        else:
            S[x], S[delta] = domain.of(Greater)

        return Equal(Limit[x:oo](fx), A)
    else:
        assert not x.is_integer and x.is_real
        assert not delta.is_integer and delta.is_real

        if domain.is_And:
            lt, gt = domain.args
            xx0, S[delta] = lt.of(Less)
            if xx0.is_Abs:
                S[x], x0 = xx0.of(Abs[Expr - Expr])
                assert x0.is_real

                S[xx0], S[0] = gt.of(Greater)
                dir = 0
            else:
                [*args] = xx0.of(Add)
                for i, arg in enumerate(args):
                    if arg == x:
                        del args[i]
                        x0 = -Add(*args)
                        dir = S.Infinitesimal
                        break
                    if arg == -x:
                        del args[i]
                        x0 = Add(*args)
                        dir = -S.Infinitesimal
                        break
        elif domain.is_Greater:
            dir = -S.Infinitesimal
            x0 = oo
        elif domain.is_Interval:
            assert domain.left_open and domain.right_open
            a, b = domain.args
            if b.is_Infinity:
                dir = -S.Infinitesimal
                x0 = oo
                assert a == delta
            else:
                assert delta == b - a
                if b._has(delta):
                    x0 = a
                    dir = S.Infinitesimal
                elif a._has(delta):
                    x0 = b
                    dir = -S.Infinitesimal

        return Equal(Limit[x:x0 + dir](fx).simplify(), A)


@prove
def prove(Eq):
    from Lemma import Calculus

    x, x0, a = Symbol(real=True)
    f = Function(real=True, shape=())
    epsilon, delta = Symbol(real=True, positive=True)
    Eq << apply(Any[delta](All[x: (abs(x - x0) > 0) & (abs(x - x0) < delta)](abs(f(x) - a) < epsilon)))

    Eq << Eq[1].this.apply(Calculus.Eq.Is.Any_All.limit_definition)





if __name__ == '__main__':
    run()

# created on 2020-04-04
# updated on 2021-10-02