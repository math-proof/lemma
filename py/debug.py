import functools, traceback, os, inspect
from py import exec_generator


def compare_element(v, _v):
    if isinstance(v, dict):
        if isinstance(_v, dict):
            yield from compare(v, _v)
        else:
            return 'type'

    elif isinstance(v, (list, tuple)):
        if isinstance(_v, (list, tuple)):
            yield from compare(v, _v)
        else:
            return 'type'

    else:
        try:
            b = v == _v
            if hasattr(b, 'all'):
                if b.all():
                    ...
                else:
                    return 'value'
            elif b:
                ...
            else:
                return 'value'
        except RuntimeError as e:
            return e


def compare(obj, _obj):

    if isinstance(obj, dict) and isinstance(_obj, dict):
        if len(obj) != len(_obj):
            print("keys lengths are not equal!")
            if len(obj) > len(_obj):
                print("missing keys in the right hand side:", obj.keys() - _obj.keys())
            else:
                print("missing keys in the left hand side:", _obj.keys() - obj.keys())

        for key, v in obj.items():
            if key not in _obj:
                print(f"{key} does not exist in the right hand side")
                continue
            keys = []
            if err_type := exec_generator(compare_element(v, _obj[key]), keys):
                print(f'{err_type} error, at key = {key}')
                yield key
            yield from keys

    elif isinstance(obj, (list, tuple)) and isinstance(_obj, (list, tuple)):
        if len(obj) != len(_obj):
            print("lengths are not equal!")
            print(len(obj), len(_obj))
            return

        for key, [v, _v] in enumerate(zip(obj, _obj)):
            keys = []
            if err := exec_generator(compare_element(v, _v), keys):
                print('index =', key, 'error info:', err)
                yield key
            yield from keys

def default_on_error(default=None):
    """
    Decorator that catches exceptions and returns a default value.
    """
    def decorator(func):
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            try:
                return func(*args, **kwargs)
            except Exception as e:
                traceback.print_exc()
                args = '\n'.join(f"{arg!r}" for arg in args)
                args = f"\nARGS:\n{args}" if args else ''
                kwargs = '\n'.join(f"{key} = {value!r}" for key, value in kwargs.items())
                kwargs = f"\nKWARGS:\n{kwargs}" if kwargs else ''
                print(f"Error parsing:\n{e}{args}{kwargs}")
                return default
        return wrapper
    return decorator

try:
    import debugpy
    class attach:
        instance = None
        def __new__(cls, *args, **kwargs):
            if args:
                return attach(**kwargs).settrace(*args)
            if cls.instance is None:
                cls.instance = self = super().__new__(cls)
            else:
                self = cls.instance
                if 'port' in kwargs:
                    assert self.port == kwargs['port'], "port mismatch"
                if 'reverse' in kwargs:
                    assert self.reverse == kwargs['reverse'], "reverse mismatch"
            return self

        def __init__(self, port=5678, reverse=True):
            # __init__ will be called automatically after __new__ is called
            if hasattr(self, "_is_attached"):
                return
            self.port = port
            self.reverse = reverse
            self._is_attached = False

        def __ensure_debugger(self):
            if self._is_attached:
                return
            self._is_attached = True
            if "RAY_DEBUG" in os.environ:
                # using ray distributed debugger for VSCode
                return breakpoint()
            port = self.port
            if self.reverse:
                '''launch.json
{
    "name": "Python: Reverse-Attach",
    "type": "debugpy",
    "request": "attach",
    "listen": {
        "host": "0.0.0.0",
        "port": 5678
    },
    "pathMappings": [
        {
            "localRoot": "${workspaceFolder}",
            "remoteRoot": "${workspaceFolder}"
        }
    ]
}
'''
                localhost = os.getenv("localhost", "127.0.0.1")
                print(f"connect to {localhost}:{port}")
                debugpy.connect((localhost, port))
            else:
                '''launch.json
{
    "name": "Python: Forward-Attach",
    "type": "debugpy",
    "request": "attach",
    "connect": {
        "host": "127.0.0.1",
        "port": 5678
    },
    "pathMappings": [
        {
            "localRoot": "${workspaceFolder}",
            "remoteRoot": "${workspaceFolder}"
        }
    ]
}
'''
                try:
                    print(f"try to listen to 0.0.0.0:{port}")
                    debugpy.listen(("0.0.0.0", port))
                except RuntimeError as e:
                    if 'Address already in use' in str(e):
                        # Ask OS to pick a free port
                        host, port = debugpy.listen(("0.0.0.0", 0))
                        print(f"Debugger listening on {host}:{port}")
                        self.port = port
                    else:
                        raise e
            print("debugpy.wait_for_client()")
            debugpy.wait_for_client()
            print("starting debugging")
            debugpy.breakpoint()

        def breakpoint(self, func):
            """
            Decorator that set a breakpoint for a remote function within a worker/driver
            """
            if inspect.iscoroutinefunction(func):
                @functools.wraps(func)
                async def wrapper(*args, **kwargs):
                    self.__ensure_debugger()
                    return await func(*args, **kwargs)
            elif inspect.isasyncgenfunction(func):
                @functools.wraps(func)
                async def wrapper(*args, **kwargs):
                    self.__ensure_debugger()
                    async for value in func(*args, **kwargs):
                        yield value
            else:
                @functools.wraps(func)
                def wrapper(*args, **kwargs):
                    self.__ensure_debugger()
                    return func(*args, **kwargs)
            return wrapper

        def settrace(self, func):
            match func:
                case staticmethod() | classmethod():
                    return type(func)(self.breakpoint(func.__func__))
                case property():
                    return type(func)(
                        self.breakpoint(func.fget),
                        func.fset,
                        func.fdel,
                        func.__doc__,
                    )
                case _:
                    return self.breakpoint(func)
except ImportError:
    ...
