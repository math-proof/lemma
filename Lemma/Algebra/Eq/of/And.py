from util import *

def indexOf(equivalent_classes, a):
    for i, clazz in enumerate(equivalent_classes):
        if a in clazz:
            return i

def transit(eqs, reverse=False):
    equivalent_classes = []
    for eq in eqs:
        a, b = eq.of(Equal)
        index_a = indexOf(equivalent_classes, a)
        index_b = indexOf(equivalent_classes, b)
        if index_a is None:
            if index_b is None:
                equivalent_classes.append({a: 1, b: 1})
            else:
                clazz = equivalent_classes[index_b]
                clazz[a] = 1
                clazz[b] += 1
        else:
            if index_b is None:
                clazz = equivalent_classes[index_a]
                clazz[b] = 1
                clazz[a] += 1
            else:
                if index_a == index_b:
                    print('%s = %s results in a circle')
                    return

                if index_a > index_b:
                    index_a, index_b = index_b, index_a

                b_class = equivalent_classes.pop(index_b)
                a_class = equivalent_classes[index_a]
                for key, count in b_class.items():
                    if key in a_class:
                        a_class[key] += count
                    else:
                        a_class[key] = count

                a_class[a] += 1
                a_class[b] += 1

    equivalent_class, = equivalent_classes
    unique_keys = []
    for a, count in equivalent_class.items():
        if count == 1:
            unique_keys.append(a)

    a, b = unique_keys
    if reverse:
        b, a = a, b

    return Equal(b, a)


@apply
def apply(et, reverse=False):
    return transit(et.of(And), reverse=reverse)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic, Logic

    x, y, a, b, c, d = Symbol(etype=dtype.real)
    Eq << apply(Equal(b, x) & Equal(x, a) & Equal(c, a) & Equal(d, c) & Equal(b, y))

    Eq << Logic.And_And.of.And.apply(Eq[0], index=None)

    Eq <<= Logic.Eq.of.Eq.Eq.apply(Eq[-5], Eq[-4]), Logic.Eq.of.Eq.Eq.apply(Eq[-3], Eq[-2])

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[-3], Eq[-1])

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[-1], Eq[-3])




if __name__ == '__main__':
    run()
# created on 2022-01-04

