import traceback
import sys
sys.path.insert(0,'.')
# Mimic loading the module's prove
try:
    from Lemma.Finset.Any.And.of.Eq_Adjoint.Imp_Gt_0 import Cholesky
    print('imported', Cholesky.__file__)
    # run prove via project's run if available on module
    if hasattr(Cholesky, 'prove'):
        print('has prove')
except Exception as e:
    traceback.print_exc()
