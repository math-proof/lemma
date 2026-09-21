from util import *


@apply
def apply(given, epsilon=None, delta=None):
    return Any_All(given, epsilon, delta)


def Any_All(given, epsilon=None, delta=None, upper=None):
    (fx, (x, x0)), a = given.of(Equal[Limit])
    x0, direction = x0.clear_infinitesimal()

    if isinstance(epsilon, Basic):
        assert not epsilon.is_given
        assert epsilon.domain.min().is_Infinitesimal
        if upper:
            assert epsilon < upper
    else:
        if epsilon is None:
            epsilon = 'epsilon'
        kwargs = dict(real=True, var=epsilon)
        if upper:
            assert upper > 0
            kwargs['domain'] = Interval(0, upper, left_open=True, right_open=True)
        else:
            kwargs['positive'] = True
        epsilon = given.generate_var(x, **kwargs)

    if fx.is_real:
        assert a.is_extended_real
    else:
        assert fx.is_complex
        assert a.is_extended_complex

    kwargs = {}
    if x.is_integer:
        kwargs['integer'] = True
        kwargs['var'] = 'N' if delta is None else delta
    else:
        kwargs['real'] = True
        kwargs['var'] = 'delta' if delta is None else delta

    if isinstance(delta, Basic):
        assert not delta.is_given
        assert delta > 0
    else:
        delta = given.generate_var(x, positive=True, **kwargs)

    assert not x.is_integer or x.is_integer and x0.is_infinite
# https://en.wikipedia.org/wiki/Limit_of_a_function
    if x0.is_Infinity:
# https://en.wikipedia.org/wiki/Limit_of_a_function
# Limits at infinity
        cond = x > delta
    elif x0.is_NegativeInfinity:
        cond = x < -delta
# "epsilon–delta definition of limit"
# https://en.wikipedia.org/wiki/(%CE%B5,_%CE%B4)-definition_of_limit
    elif x.shape:
        cond = (0 < Norm(x - x0)) & (Norm(x - x0) < delta)
    elif not x.is_real or direction == 0:
        cond = (0 < abs(x - x0)) & (abs(x - x0) < delta)
    elif direction > 0:
        cond = Interval(x0, x0 + delta, left_open=True, right_open=True)
        # cond = (0 < x - x0) & (x - x0 < delta)
    elif direction < 0:
        cond = Interval(x0 - delta, x0, left_open=True, right_open=True)
        # cond = (0 < x0 - x) & (x0 - x < delta)
    else:
        ...

    if a.is_Infinity:
# https://en.wikipedia.org/wiki/One-sided_limit
        epsilon_constraint = fx > epsilon
    elif a.is_NegativeInfinity:
        epsilon_constraint = fx < -epsilon
    else:
        epsilon_constraint = abs(fx - a) < epsilon

    return Any[delta](All[x:cond](epsilon_constraint))


@prove(provable=False)
def prove(Eq):
    x, x0, a = Symbol(real=True)
    f = Function(real=True, shape=())
    Eq << apply(Equal(Limit[x:x0 + S.Infinitesimal](f(x)), a))

    


if __name__ == '__main__':
    run()
# https://baike.baidu.com/item/戴德金定理
# https://baike.baidu.com/item/单调有界定理# 3
# The monotone bounded convergence theorem
# created on 2020-04-03
# updated on 2023-04-17
