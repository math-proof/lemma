import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Algebra.MonoidAlgebra.InversionTwist.Part3
open GroupRing

/--
[inversion_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MonoidAlgebra/InversionTwist.lean)
-/
@[path]
private lemma main
-- given
  [CommRing R] [CommGroup G]
  (g : G) (r : R) :
-- imply
  inversion R G (MonoidAlgebra.single g r) = MonoidAlgebra.single g⁻¹ r := by
-- proof
  apply inversion_single

-- created on 2026-10-10
