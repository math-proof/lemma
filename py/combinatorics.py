import random
from py import prod


def HeapPermutation(k, A):
    '''
    https://en.wikipedia.org/wiki/Heap%27s_algorithm
    '''
    
    if k == 1:
        yield A
    else:
        # Generate permutations with kth unaltered, Initially k == length(A)
        yield from HeapPermutation(k - 1, A)
        
        # Generate permutations for kth swapped with each k-1 initial
        for i in range(k - 1):
            # Swap choice dependent on parity of k (even or odd)
            if k & 1:
                A[0], A[k - 1] = A[k - 1], A[0]
            else:
                A[i], A[k - 1] = A[k - 1], A[i]
            
            yield from HeapPermutation(k - 1, A)


def generate_all_permutation(A):
    yield from HeapPermutation(len(A), A)


def skip_first_permutation(A):
    generator = HeapPermutation(len(A), A)
    next(generator)
    yield from generator


import heapq


class TopKHeap:

    def __init__(self, k):
        self.data = []
        self.k = k

    def __str__(self):
        return str(self.data)
    
    __repr__ = __str__
    
    def push(self, num):
        #internally, it is a minimum heap!
        if len(self.data) < self.k:
            heapq.heappush(self.data, num)
        elif num > self.data[0]:
            heapq.heapreplace(self.data, num)

    def topk(self):
        
        arr = []
        while self.data:
            a = heapq.heappop(self.data)
            arr.append(a)
            
        arr.reverse()
        return arr
    

# return a combination of k elements selected among {0, 1, 2, n - 2, n - 1};
def generate_combination(n, k):
    assert n >= k and k > 0, "n >= k && k > 0"
    x = [0] * k
    i = 0
    while True:
        if x[i] <= n - (k - i):
            if i == k - 1:
                yield [*x]
            else:
                i += 1
                x[i] = x[i - 1]
            x[i] += 1
        else:
            i -= 1
            x[i] += 1  # backtracking to the previous index.
        if x[0] > n - k:
            break


def sigmar(x, k):
    if k == 0:
        return 1
    if k == 1:
        return sum(x)
    sigmar = 0
    for indices in generate_combination(len(x), k):
        sigmar += prod((x[i] for i in indices))
    return sigmar

def random_combination(n, k, reverse=True):
    k = min(k, n)
    all_indices = [*range(n)]
    indices = [all_indices.pop(random.randrange(0, len(all_indices))) for _ in range(k)]
    indices.sort(reverse=reverse)
    return indices

if __name__ == '__main__':
    for a in generate_all_permutation([*range(4)]):
        print(a)
