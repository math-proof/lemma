from util import *






@apply
def apply(self):

    def next_free_symbol(ch):
        return chr(ord(ch) + 1)

    x = self.of(Norm)
    shape = x.shape
    size = len(shape)

    ch = 'i'
    excludes = set()
    limits = []
    d = -1
    indices = []
    for d in range(-1, -size - 1, -1):
        var = self.generate_var(excludes, var=ch, integer=True)
        limits.append((var, 0, shape[d]))
        indices.append(var)
        excludes.add(var)
        ch = next_free_symbol(ch)

    indices.reverse()
    return Equal(self, sqrt(Sum(Abs(x[tuple(indices)]) ** 2, *limits)))


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(Norm(x))


if __name__ == '__main__':
    run()

# created on 2020-12-25
