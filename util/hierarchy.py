import time, os, re
from util.utility import user
from collections import defaultdict
from util.search import py_to_module, read_directory, read_all_files, \
    yield_callee_from_py, axiom_directory, is_py_theorem
from os.path import basename

import datetime
from std.file import Text
os.environ['MYSQL_DATABASE'] = 'axiom'
from std import MySQL

def read_all_axioms(dir):

    for directory in read_directory(dir):
        print(directory)
        for py in read_all_files(directory, '.py'):
            if basename(py) != "__init__.py":
                yield py, py[0:-2] + 'php'
            else:
                yield py, py[0:-len('/__init__.py')] + '.php'


def retrieve_all_dependency(): 
    print("axiom_directory =", axiom_directory())
    for py, php in read_all_axioms(axiom_directory()):
        source = py_to_module(php)

        count = defaultdict(int)
        if is_py_theorem(py):
            print("py =", py)
            for to in yield_callee_from_py(py):
                count[to] += 1

            yield source, count


def insert_into_hierarchy():
    data = []
    for caller, counts in retrieve_all_dependency(): 
        for callee, count in counts.items():
#             print(user, caller, callee, count)
            args = user, caller, callee, count
            data.append(args)
        
    MySQL.instance.execute(f"delete from hierarchy where user = '{user}'")
    
    MySQL.instance.load_data('hierarchy', data)

    
def topological_sort():
    graph = {}
    axiomSet = set()
    for caller, counts in retrieve_all_dependency(): 
        for callee, count in counts.items():
            if caller not in graph:
                graph[caller] = []
            # caller is dependent on callee, so callee is a parent of caller
            graph[caller].append(callee)                        
            axiomSet.add(callee)
        axiomSet.add(caller)
        
    axiomSet -= graph.keys()
    if axiomSet:
        for module in axiomSet:
            graph[module] = []
             
    from sympy.utilities.iterables import topological_sort_depth_first
    
    G = topological_sort_depth_first(graph)
    return G


def update_timestamp_for_axiom(module, create_time):
    import Lemma
    module = eval('axiom.' + module)
#     print(module, 'is created on', create_time)
    file = module.__file__
    original_create_time = None
    original_update_time = None
    for line in Text(file):
        if m := re.match(r'(?:    )*#created on (\d\d\d\d-\d\d-\d\d)', line):
            original_create_time = m[1]
            
        if m := re.match(r'(?:    )*#updated on (\d\d\d\d-\d\d-\d\d)', line):
            original_update_time = m[1]
            
    if original_update_time or original_create_time:
        return
    
    Text(file).append("# created on " + create_time[:10])
    Text(file).append("# updated on " + create_time[:10])
    # created on ...
    # updated on ...

    
def update_timestamp():
    G = topological_sort()

    print(len(G))
    datetime.date(2018, 1, 1)
    initial = time.mktime(datetime.date(2018, 1, 1).timetuple())
    delta = time.time() - initial
    delta /= len(G)
    
    create_times = []
    for i in range(len(G)):
        create_time = initial + delta * i
        create_time = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(create_time))
        create_times.append(create_time)
    
    for module, create_time in zip(G, create_times):
        update_timestamp_for_axiom(module, create_time)


# from util.hierarchy import update_timestamp
# update_timestamp()
if __name__ == '__main__':
    insert_into_hierarchy()
    # update_timestamp()
