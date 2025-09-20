from util import *


def subs_limits_with_epitome(self, epitome):
    if self.is_ExprWithLimits:
        if epitome.func == self.func and len(epitome.limits) == len(self.limits):
            _self = self
            for _v, v in zip(epitome.variables, self.variables):
                if _v != v:
                    _self = _self.limits_subs(v, _v)
            return _self
    return self


@apply
def apply(imply):
    e, S = imply.of(Element)

    variables, expr, base_set = S.image_set()

    variables_ = Wild('z', **variables.type.dict)
    assert variables_.shape == variables.shape
    e = subs_limits_with_epitome(e, expr)
    dic = e.match(expr.subs(variables, variables_))

    variables_ = dic[variables_]
    if variables_.shape != variables.shape:
        indices = [slice(0, length) for length in variables.shape]
        variables_ = variables_[indices]

    assert variables_.shape == variables.shape
    return Element(variables_, base_set)


@prove
def prove(Eq):
    from Lemma import Set
    x, y = Symbol(integer=True)
    f = Function(integer=True)
    s = Symbol(etype=dtype.integer)

    Eq << apply(Element(f(y), imageset(x, f(x), s)))

    Eq << Set.In.Imageset.of.In.apply(Eq[1], f=f)


if __name__ == '__main__':
    run()

# created on 2020-09-30
