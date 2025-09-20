from flask import render_template

from util import * 
from Lemma import *
import json, re
from flask.blueprints import Blueprint
from os.path import dirname
from std import json_encode
 
debug = Blueprint('debug', __name__) 

 
@debug.route('/debug/<symbol>', methods=['GET'])
def symbol(symbol):
    
    statements = []
    for script, latex in MySQL.instance.select(f"select script, latex from debug where symbol = '{symbol}'"):
        latex = latex.strip()
        latex = json.loads(latex)
        
        script = json.loads(script)

        for i in range(len(latex)):
            statements.append(dict(script=script[i], latex=latex[i]))
        script = '\n'.join(script)
    
    statements.append(dict(script='', latex=''))
    
    return render_template('debug.html', symbol=symbol, statements=statements, script=script)


@debug.route('/debug', methods=['GET', 'POST'])
def index():
    module = request.args.get('module', None)
    print('module =', module)

    python_file = dirname(dirname(__file__)) + "/" + module.replace(".", "/") + ".py";
    
    code = request.form.get('code')
    if code:
        code = code.replace('\r\n', '\n')
        with open(python_file, "w") as file:
            file.write(code)
    else:
        with open(python_file, "r") as file:
            code = file.read()
    
    code = code.replace("\\", "\\\\");
    code = code.replace("`", "\\`");
    
    return render_template('module.html', title=module, code=code)

 
from flask import request

__globals__ = globals()

    
def local_eval(python, __globals__): 
    try:
        result = eval(python, __globals__)
    except SyntaxError: 
        try:
            exec(python, __globals__)
        except Exception as e:
            return str(e)
    
        return ''

    except Exception as e:
        try:
            print(e)
            e = str(e)
            return e
        except:
            return str(type(e))        
    
    try:
        if isinstance(result, type) or not hasattr(result, "is_Basic"):
            latex = str(result)
        else:
            latex = r'\[%s\]' % result.latex
    except Exception as e:
        print(e)
        latex = f"{type(e).__name__}: {e}"
        
    return latex

        
class Cout:
    def __init__(self):
        self._buff = []
 
    def write(self, s):
        print(s, file=stdout, end='')
        self._buff.append(s)
        
    def clear(self):
        self._buff.clear()

Cout = Cout()
stdout = sys.stdout
sys.stdout = Cout

@debug.route('/debug/exec', methods=['POST', 'GET'])
def execute():
    Cout.clear()
    
    python = request.json.get('py')
    
    ret = None
    err = None
    
    try:
        ret = eval(python, __globals__)
    except SyntaxError:
        try:
            exec(python, __globals__)                
        except TypeError:
            for line in python.splitlines():
                exec(compile_definition_statement(line), __globals__)                
    except Exception as e:
        typname = type(e).__name__
        print(type(e), e)
        msg = str(e)
        err = {}
        err[typname] = msg
    
    if isinstance(ret, tuple):
        ret = ''.join([to_str(r) for r in ret])
    elif ret is not None:        
        ret = to_str(ret)
        
    return json_encode(dict(log=''.join(Cout._buff), ret=ret, err=err))


@debug.route('/debug/eval', methods=['POST', 'GET'])
def evaluate():
    Cout.clear()
    
    python = request.json.get('py')
    
    ret = None
    err = None
    
    if request.json.get('multiple'):
        python = python.splitlines()
        latex = [local_eval(line, __globals__) for line in python]
        
        ret = utility.json_encode(latex)
    else:
        ret = eval(python, __globals__)
    
    if isinstance(ret, tuple):
        ret = ''.join([to_str(r) for r in ret])
    elif ret is not None:        
        ret = to_str(ret)
        
    return json_encode(dict(log=''.join(Cout._buff), ret=ret, err=err))

def to_str(result):
    if isinstance(result, type) or not hasattr(result, "is_Basic"):
        return str(result)
    else:
        return r'\[%s\]' % result.latex
    

@debug.route('/debug/compile', methods=['POST'])
def compile_python_file():
    python = request.form.get('py')
    
    try:
        with open(python, 'r', encoding='utf8') as file:
            eval(file.read(), __globals__) 
    except Exception as e:
        typname = type(e).__name__
        print(type(e), e)
        msg = str(e)                
        return f'{typname}: {msg}'
    
    return 'success'    

    
@debug.route('/debug/hint', methods=['POST', 'GET'])
def hint():
    
    symbol = request.args.get('symbol')
    if symbol is None:
        symbol = request.form.get('symbol')

    return utility.json_encode(extract_latex(symbol))


