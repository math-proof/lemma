import Mathlib
import Initialize.Tactic.Attr.Basic
open Module FiniteDimensional


/--
[finrank_orthogonal_of_Nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FinrankOrthogonal.lean)
-/
@[path]
private lemma main
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {B : LinearMap.BilinForm k V}
  {W : Submodule k V}
-- given
  (hB : B.Nondegenerate) :
-- imply
  finrank k (B.orthogonal W) = finrank k V - finrank k W := by
-- proof
  apply LinearMap.BilinForm.finrank_orthogonal hB W


-- created on 2026-10-23
-- updated on 2026-10-26
