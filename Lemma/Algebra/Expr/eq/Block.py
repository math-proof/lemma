from util import *

def squeeze_shape(shape):
    shapes = []
    indices = []
    for index, s in enumerate(shape):
        if s == 1:
            indices.append(index)
        else:
            shapes.append(s)
    return tuple(shapes), indices


def trim_leading(shape):
    while shape:
        if shape[0] == 1:
            shape = shape[1:]
        else:
            break

    return shape


def split(self, *pivot, axis=0):
    rhs = self
    shape = self.shape
    for k in pivot:
        if k < 0:
            k += shape[axis]

        prev_slices = [slice(None)] * axis
        former = rhs[prev_slices + [slice(0, k)]]
        latter = rhs[prev_slices + [slice(k, shape[axis])]]
        assert former.shape == trim_leading(shape[:axis] + (k,) + shape[axis + 1:])
        if latter.shape == trim_leading(shape[:axis] + (shape[axis] - k,) + shape[axis + 1:]):
            rhs = BlockMatrix[axis](former, latter, shape=shape)
        else:
            shape_squeezed, indices = squeeze_shape(shape[:axis] + (shape[axis] - k,) + shape[axis + 1:])
            assert latter.shape == shape_squeezed
            index_omitted, = indices
            former = Transpose[0, index_omitted](former)
#           shape = *shape[:index_omitted], shape[index_omitted], shape[shape[:index_omitted] + 1:]
#                   -----------------swap-----------------------
#           shape = shape[index_omitted], *shape[:index_omitted], shape[shape[:index_omitted] + 1:]
            rhs = Transpose[0, index_omitted]([former, latter])

        assert rhs.shape == shape
        axis += 1

    return rhs


@apply
def apply(self, *pivot, axis=0):
    return Equal(self, split(self, *pivot, axis=axis), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    m = Symbol(integer=True, positive=True)
    A = Symbol(real=True, shape=(m, m, m, m, m))
    i, j = Symbol(domain=Range(1, m))
    Eq << apply(A, i, j, axis=2)

    t = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], t)

    k = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], k)

    l = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], l)

    p = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], p)





if __name__ == '__main__':
    run()
# created on 2023-03-31
# updated on 2023-04-29

