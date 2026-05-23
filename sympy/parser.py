from std import Object, computed
import sys, json

def parse_args(argv, args, kwargs):
    for i, arg in enumerate(argv):
        if arg.startswith('--'):
            args.extend(argv[:i])
            return parse_kwargs(argv[i:], args, kwargs)
    else:
        args.extend(argv)

def parse_kwargs(argv, args, kwargs):
    def get_val(value):
        try:
            return json.loads(value)
        except:
            return value

    name = None
    for i, arg in enumerate(argv):
        if arg.startswith('--'):
            if name is not None:
                if kwargs[name] is None:
                    kwargs[name] = True

            name = arg[2:]
            if '=' in name:
                index = name.index('=')
                name, arg = name[:index], name[index + 1:]
                kwargs[name] = get_val(arg)
                name = None
        elif name is None:
            return parse_args(argv[i:], args, kwargs)

        elif name in kwargs:
            if not isinstance(kwargs[name], list):
                kwargs[name] = [kwargs[name]]
            kwargs[name].append(get_val(arg))
        else:
            kwargs[name] = value = get_val(arg)
            if value is None:
                name = None

    if name is not None:
        if kwargs[name] is None:
            kwargs[name] = True

    return kwargs

def argparse():
    argv = sys.argv[1:]
    args = []
    kwargs = Object()
    parse_args(argv, args, kwargs)

    for key in [*kwargs.keys()]:
        _key = key.replace('-', '_')
        if _key != key:
            kwargs[_key] = kwargs.pop(key)

    return args, kwargs

class ArgumentParser:
    def __init__(self):
        self.args, self.kwargs = argparse()

    @computed
    def instance(cls):
        return cls()
