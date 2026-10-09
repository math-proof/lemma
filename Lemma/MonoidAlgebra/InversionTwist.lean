import Mathlib
import sympy.Basic
import sympy.Algebra.MonoidAlgebra.InversionTwist

open GroupRing

/--
[inversion_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MonoidAlgebra/InversionTwist.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommGroup G]
-- given
  (g : G) (r : R) :
-- imply
  inversion R G (MonoidAlgebra.single g r) = MonoidAlgebra.single g⁻¹ r := by
-- proof
  apply inversion_single


/--
[inversion_involution](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MonoidAlgebra/InversionTwist.lean)
-/
@[path]
private lemma invol
  [CommRing R] [CommGroup G]
-- given
  (x : MonoidAlgebra R G) :
-- imply
  inversion R G (inversion R G x) = x := by
-- proof
  apply inversion_involution


/--
[val_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MonoidAlgebra/InversionTwist.lean)
-/
@[path]
private lemma smul_val
  [CommRing R] [CommGroup G] [AddCommGroup A]
  [Module (MonoidAlgebra R G) A]
-- given
  (r : MonoidAlgebra R G) (a : InversionTwist A) :
-- imply
  (r • a).val = inversion R G r • a.val := by
-- proof
  apply InversionTwist.val_smul


-- created on 2026-10-09
