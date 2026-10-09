from py.format import format_number

def get_statistics(tensor, json=True):
    tensor = tensor.float()
    keys = 'mean', 'std', 'min', 'max', 'sum'
    values = [getattr(tensor, key)() for key in keys]
    values = [value.item() for value in values]
    if json:
        return {key : values[i] for i, key in enumerate(keys)}
    return values

def plotFunction(x, *y, label=None):
    """_summary_

    Args:
        x (np.ndarray): x = linspace(-pi * 2, 2 * pi, 1000)
        label (list, optional): ['sin(x)', 'x * (π ** 2 - x ** 2) / (π ** 2 + x ** 2)']

    Example:
    ```
    plotFunction(
        x,
        sin(x),
        x * (pi ** 2 - x ** 2) / (pi ** 2 + x ** 2),
        label=['sin(x)', 'x * (π ** 2 - x ** 2) / (π ** 2 + x ** 2)'])
    ```
    """
    from matplotlib import pyplot
    fig = pyplot.figure(num=1, dpi=120)
    ax = pyplot.subplot(111)

    ax = pyplot.gca()  # get current axis
    ax.spines["right"].set_color("none")
    ax.spines["top"].set_color("none")
    ax.xaxis.set_ticks_position("bottom")
    ax.yaxis.set_ticks_position("left")
    ax.spines["bottom"].set_position(("data", 0))
    ax.spines["left"].set_position(("data", 0))

    if label is None:
        label = [f"Fig {i}" for i in range(len(y))]

    for i, (y, label) in enumerate(zip(y, label)):
        ax.plot(x, y, label=label)

    # ax.set_xlim(0,2)
    ax.set_xlabel("line", color="cyan")
    # pyplot.draw()
    pyplot.legend()
    pyplot.show()


def print_jsonl(data, line_tag=None):
    [*keys] = data[0].keys()
    if line_tag:
        for i, obj in enumerate(data):
            obj[line_tag] = i + 1
        keys.insert(0, line_tag)

    def format(data):
        if isinstance(data, str):
            return data
        if isinstance(data, float):
            return format_number(data)
        return str(data)

    rows = len(data) + 1
    cols = len(keys)
    table_cells = [keys] + [[format(data[i][key]) for key in keys] for i in range(len(data))]
    max_col_width = [max(len(table_cells[i][j]) for i in range(rows)) for j in range(cols)]
    for i in range(rows):
        for j in range(cols):
            if diff := max_col_width[j] - len(table_cells[i][j]):
                table_cells[i][j] = ' ' * diff + table_cells[i][j]

    print('\n'.join(('\t'.join(row) for row in table_cells)))

if __name__ == '__main__':
    import random
    data = [dict(loss=random.random(), accuracy=random.random()) for i in range(10)]
    print_jsonl(data)

    import numpy
    from numpy import linspace
    x = linspace(-2, 2, 1000)
    plotFunction(x, numpy.tanh(x))

