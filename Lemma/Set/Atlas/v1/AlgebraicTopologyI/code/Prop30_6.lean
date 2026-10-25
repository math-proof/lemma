import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Prop30_6
open Matrix SymmetricBilinearForms


namespace SymmetricBilinearForms

/--
[nondegenerate_symm_bilinearForm_F2_classification](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Prop30_6.lean)
-/
@[path]
lemma nondegenerate_symm_bilinearForm_F2_classification
  [AddCommGroup V]
  [Module (ZMod 2) V]
  [Module.Finite (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V}
-- given
  (hB_symm : B.IsSymm)
  (hB_nondeg : B.Nondegenerate) :
-- imply
  ∃ (a b : ℕ) (e : V ≃ₗ[ZMod 2] (Fin a → ZMod 2) × (Fin b → Fin 2 → ZMod 2)), (LinearMap.BilinForm.congr e) B = BilinFormZMod2.standardF2Form a b :=
-- proof
  BilinFormZMod2.exists_isometry_standardF2Form B hB_symm hB_nondeg

end SymmetricBilinearForms


-- created on 2026-10-23
