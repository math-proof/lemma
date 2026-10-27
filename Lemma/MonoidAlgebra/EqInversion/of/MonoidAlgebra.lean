import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Algebra.MonoidAlgebra.InversionTwist.Part3
open GroupRing

/--
[inversion_involution](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MonoidAlgebra/InversionTwist.lean)
-/
@[path]
private lemma main
-- given
  [CommRing R] [CommGroup G]
  (x : MonoidAlgebra R G) :
-- imply
  inversion R G (inversion R G x) = x := by
-- proof
  apply inversion_involution

-- created on 2026-10-10
