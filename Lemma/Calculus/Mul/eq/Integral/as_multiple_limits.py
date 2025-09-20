from util import *
import traceback


@apply
def apply(self):
    try:
        (fx, (x, *xab)), (fy, (y, *yab)) = self.of(Integral * Integral)
    except Exception as e:
        print(e)
        print('self =', self)
        print("self.of(Integral * Integral) =", self.of(Integral * Integral))
        print('Integral.__subclasses__() =', Integral.__subclasses__())
        print('Integral.is_abstract =', Integral.is_abstract)


        traceback.print_exc()

    if x == y:
        _y = self.generate_var(excludes=x, **y.type.dict)
        fy = fy._subs(y, _y)
        y = _y
    rhs = Integral(fx * fy, (x, *xab), (y, *yab))
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Calculus

    a, b, c, d, x = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Integral[x:a:b](f(x)) * Integral[x:c:d](g(x)))

    Eq << Eq[-1].this.rhs.apply(Calculus.Integral.limits.separate)

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()
# created on 2020-06-09
