import Mathlib
import sympy.Basic
import sympy.algebra.monoid_algebra.inversion_twist
open GroupRing


/--
[val_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MonoidAlgebra/InversionTwist.lean)
-/
@[path]
private lemma main
-- given
  [CommRing R] [CommGroup G] [AddCommGroup A]
  [Module (MonoidAlgebra R G) A]
  (r : MonoidAlgebra R G) (a : InversionTwist A) :
-- imply
  (r • a).val = inversion R G r • a.val := by
-- proof
  apply InversionTwist.val_smul


-- created on 2026-10-10
