from util import *



@apply
def apply(equality_A, equality_B):
    image_B, A = equality_A.of(Equal)
    image_A, B = equality_B.of(Equal)

    gb, b, S[B] = image_B.image_set()
    fb, a, S[A] = image_A.image_set()

    return Equal(Card(A), Card(B))




@prove
def prove(Eq):
    from Lemma import Set
    n, m = Symbol(integer=True, positive=True)
    A = Symbol(etype=dtype.integer[n])
    a = Symbol(integer=True, shape=(n,))

    B = Symbol(etype=dtype.integer[m])
    b = Symbol(integer=True, shape=(m,))

    f = Function(integer=True, shape=(m,))
    g = Function(integer=True, shape=(n,))

    Eq << apply(Equal(Cup[a:A](f(a).set), B), Equal(Cup[b:B](g(b).set), A))

    Eq << Set.CardCup.le.Sum_Card.apply(*Eq[0].lhs.args)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Set.CardCup.le.Sum_Card.apply(*Eq[1].lhs.args)

    Eq << Eq[-1].subs(Eq[1])

    Eq <<= Eq[-3] & Eq[-1]


if __name__ == '__main__':
    run()

# created on 2020-07-31
