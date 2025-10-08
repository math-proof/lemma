from util import *


def __add__(lhs, rhs, deep, simplify):
    if deep and lhs.is_Piecewise and rhs.is_Piecewise:
        return add(lhs.args, rhs.args, deep, simplify)

    ret = lhs + rhs
    if simplify:
        ret = ret.simplify()
    return ret

def add(ecs, _ecs, deep, simplify):
    piece = []
    u = S.true
    for e, c in ecs:
        args = []
        _u = S.true
        c_ = c & u
        for _e, _c in _ecs:
            _c_ = _c & _u
            _c_ = c_ & _c_
            if _c_ == False:
                continue
            args.append([__add__(e, _e, deep, simplify), _c])
            _u &= _c.invert()

        if len(args) == 1:
            piece.append((args[-1][0], c))
        else:
            args[-1][-1] = True
            e = Piecewise(*args)
            if simplify:
                e = e.simplify()
            piece.append((e, c))
        u &= c.invert()

    return Piecewise(*piece)

@apply
def apply(self, swap=False, deep=False, *, simplify=True):
    ecs, _ecs = self.of(Piecewise + Piecewise)
    if swap:
        ecs, _ecs = _ecs, ecs

    rhs = add(ecs, _ecs, deep=deep, simplify=simplify)
    if simplify and rhs.is_Piecewise:
        from Lemma.Bool.Ite_Ite.eq.Ite__Ite import flatten
        rhs = flatten(rhs)

    return Equal(self, rhs, evaluate=False)



@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    f, g, h, p = Function(real=True)
    Eq << apply(Piecewise((f(x), Element(x, A)), (g(x), True)) + Piecewise((h(x), Element(x, B)), (p(x), True)))

    Eq << Eq[-1].this.lhs.apply(Algebra.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.find(Add).apply(Algebra.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.lhs.args[1].find(Add).apply(Algebra.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.lhs.apply(Bool.Ite_Ite.eq.Ite__Ite)





if __name__ == '__main__':
    run()
# created on 2018-02-23
# updated on 2023-06-02
