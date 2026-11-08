import json, time
print('importing...', flush=True)
from run import prove_with_timing, import_module
from sympy import MySQL
from util.utility import user, json_encode
from util.utility import RetCode

pkg = 'Matrix.DetBlock_Stack_MulPowS.eq.Mul_Prod_Factorial.of.All'
old = 'Finset.DetBlock_Stack_MulPowS.eq.Mul_Prod_Factorial.vandermonde'
print('import module', flush=True)
mod = import_module(pkg)
print('proving...', flush=True)
state, lapse, latex, *lean = prove_with_timing(mod, debug=True, slow=True)
print('state=', state, 'lapse=', lapse, 'latex_len=', len(latex or ''), 'lean=', lean[:1] if lean else None, flush=True)
state_name = state.name if hasattr(state, 'name') else str(state)
# RetCode enum
if hasattr(state, 'name'):
    state_name = state.name
print('state_name=', state_name, flush=True)

# lean JSON ? ensure valid utf-8 JSON
if lean:
    lean_val = lean[0] if len(lean) == 1 else lean
    try:
        lean_json = json.dumps(lean_val, ensure_ascii=False)
        json.loads(lean_json)  # validate
    except Exception as e:
        print('lean json failed, using null:', e, flush=True)
        lean_json = None
else:
    lean_json = None

db = MySQL.instance
# delete old
n = db.execute("delete from axiom where user=%s and axiom=%s", (user, old))
print('deleted old:', n, flush=True)
n = db.execute("delete from axiom where user=%s and axiom=%s", (user, pkg))
print('deleted existing new:', n, flush=True)

# insert with connector params (safe)
sql = "insert into axiom (user, axiom, state, lapse, latex, lean) values (%s, %s, %s, %s, %s, %s)"
n = db.execute(sql, (user, pkg, state_name, lapse, latex, lean_json))
print('insert rowcount:', n, flush=True)

rows = list(db.query("select axiom, state, length(latex), lean is null from axiom where user='%s' and axiom in ('%s','%s')" % (user, pkg, old)))
print('verify:', rows, flush=True)
