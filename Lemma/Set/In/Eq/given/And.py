from util import *


@apply
def apply(el, eq):
    a, A = el.of(Element)
    _A, union_B_aset = eq.of(Equal)

    if A != _A:
        _A, union_B_aset = union_B_aset, _A

    B, aset = union_B_aset.of(Union)
    if aset != a.set:
        B, aset = aset, B

    return el, Equal(A - aset, B - aset)


@prove
def prove(Eq):
    from Lemma import Set

    a = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Element(a, A), Equal(B | a.set, A))

    Eq << Set.Eq.of.Eq.In.apply(Eq[-1], Eq[0])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2021-04-05
# updated on 2023-06-22
