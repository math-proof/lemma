import random, os, numpy as np


def extend(arr, mask, maxlength, padding_side):
    if isinstance(arr, (tuple, np.ndarray)):
        arr = [*arr]

    padding = [mask] * (maxlength - len(arr))
    if padding_side > 0:
        arr.extend(padding)
    elif padding_side < 0:
        arr = padding + arr
    else:
        for mask in padding:
            arr.insert(random.randrange(0, len(arr)), mask)

    return arr


def extend_right(arr, mask, max_length):
    if isinstance(arr, tuple):
        arr = [*arr]

    padding = [mask] * (max_length - len(arr))

    arr.extend(padding)

    return arr


def padding_right(arr, pad_token_id=0):
    maxWidth = max(len(x) for x in arr)
    # arr is a 2-dimension array
    for i in range(len(arr)):
        arr[i] = extend_right(arr[i], pad_token_id, maxWidth)
    return np.array(arr)


def padding_left(arr, pad_token_id=0, dtype=None):
    return padding(arr, pad_token_id, padding_side=-1, dtype=dtype)


def padding(arr, pad_token_id=0, padding_side=1, dtype=None):
    '''
    
    :param arr:
    :param pad_token_id:
    :param shuffle: randomly insert the padding mask into the sequence！ this is used for testing masking algorithms!
    '''

    try:
        maxWidth = max(len(x) for x in arr)
    except (TypeError, AttributeError) as _:
        return np.array(arr, dtype=dtype)

    try:
        maxHeight = max(max(len(word) for word in x) for x in arr)
        for i in range(len(arr)):
            for j in range(len(arr[i])):
                arr[i][j] = extend(arr[i][j], pad_token_id, maxHeight, padding_side)
            arr[i] = extend(arr[i], [pad_token_id] * maxHeight, maxWidth, padding_side)
    except (TypeError, AttributeError, ValueError) as _:

        # arr is a 2-dimension array
        try:
            for i in range(len(arr)):
                arr[i] = extend(arr[i], pad_token_id, maxWidth, padding_side)
        except AttributeError as _:
            # arr might be an array of string
            ...

    return np.array(arr, dtype=dtype)


def randomize(data, count):
    from py.combinatorics import random_combination
    for i in random_combination(len(data) - 1, min(count, len(data) - 1)):
        assert len(data) - i > 1
        j = random.randrange(i + 1, len(data)) # j > i
        data[i], data[j] = data[j], data[i]

    return data


def sample(data, count):
    '''
    this sampling ensure dislocation arrangement
    '''
    
    if count <= len(data):
        for i in range(count):
            if 1 < len(data) - i:
                j = random.randrange(i + 1, len(data)) # j > i
                data[i], data[j] = data[j], data[i]

        if count < len(data):
            data = data[:count]
        return data
    quotient, remainder = divmod(count, len(data))
    if remainder:
        return sample(data * quotient + sample(data[:], remainder), count)
    else:
        return sample(data * quotient, count)


def create_memmap(filename, mode='r'):
    dtype = np.dtype(filename[filename.rindex('.') + 1:])
    return np.memmap(
        filename,
        dtype=dtype,
        mode=mode,
        shape=(os.path.getsize(filename) // dtype.alignment,))


if __name__ == '__main__':
    count = 22
    data = [*range(10)]
    data_sampled = sample(data, count)
    print(data_sampled)
    assert len(data_sampled) == count
    
    if len(data) < count:
        assert {*data} & {*data_sampled} == {*data}
    