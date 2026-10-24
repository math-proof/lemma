import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.GeometricAlgebra.OppositeConjugacyInstance
open GeometricAlgebra


namespace GeometricAlgebra

/--
[swapComplement_fix_W](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyInstance.lean)
-/
@[path]
lemma swapComplement_fix_W
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {W C₁ C₂ : Submodule k V}
  {w : V}
-- given
  (hc₁ : IsCompl W C₁)
  (hc₂ : IsCompl W C₂)
  (hw : w ∈ W) :
-- imply
  swapComplement W C₁ C₂ hc₁ hc₂ w = w := by
-- proof
  simp only [swapComplement, LinearEquiv.trans_apply]
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left W C₁ hc₁ ⟨w, hw⟩]
  simp only [LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, map_zero]
  rw [Submodule.coe_prodEquivOfIsCompl' W C₂ hc₂]
  simp [add_zero]

end GeometricAlgebra

namespace GeometricAlgebra

/--
[swapComplement_map_C](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyInstance.lean)
-/
@[path]
lemma swapComplement_map_C
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {W C₁ C₂ : Submodule k V}
-- given
  (hc₁ : IsCompl W C₁)
  (hc₂ : IsCompl W C₂) :
-- imply
  C₁.map (swapComplement W C₁ C₂ hc₁ hc₂).toLinearMap = C₂ := by
-- proof
  ext v; simp only [Submodule.mem_map]; constructor
  · rintro ⟨c, hc, rfl⟩
    show swapComplement W C₁ C₂ hc₁ hc₂ c ∈ C₂
    simp only [swapComplement, LinearEquiv.trans_apply]
    rw [Submodule.prodEquivOfIsCompl_symm_apply_right W C₁ hc₁ ⟨c, hc⟩]
    simp only [LinearEquiv.prodCongr_apply, map_zero]
    rw [Submodule.coe_prodEquivOfIsCompl' W C₂ hc₂]
    simp only [Submodule.coe_zero, zero_add]
    exact (complIsomOfIsCompl W C₁ C₂ hc₁ hc₂ ⟨c, hc⟩).property
  · intro hv
    let e := swapComplement W C₁ C₂ hc₁ hc₂
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    simp only [e, swapComplement, LinearEquiv.symm_trans_apply]
    rw [Submodule.prodEquivOfIsCompl_symm_apply_right W C₂ hc₂ ⟨v, hv⟩]
    simp only [LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply, map_zero]
    rw [LinearEquiv.symm_symm]
    rw [Submodule.coe_prodEquivOfIsCompl' W C₁ hc₁]
    simp only [Submodule.coe_zero, zero_add]
    exact ((complIsomOfIsCompl W C₁ C₂ hc₁ hc₂).symm ⟨v, hv⟩).property

end GeometricAlgebra

namespace GeometricAlgebra

/--
[swapComplement_preserves_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyInstance.lean)
-/
@[path]
lemma swapComplement_preserves_sub
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {W C₁ C₂ S : Submodule k V}
-- given
  (hc₁ : IsCompl W C₁)
  (hc₂ : IsCompl W C₂)
  (hle : S ≤ W) :
-- imply
  S.map (swapComplement W C₁ C₂ hc₁ hc₂).toLinearMap = S :=
-- proof
  map_eq_of_pointwise_fix S W (swapComplement W C₁ C₂ hc₁ hc₂)
    (swapComplement_fix_W W C₁ C₂ hc₁ hc₂) hle

end GeometricAlgebra

/--
[opposite_systems_conjugacy_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyInstance.lean)
-/
@[path]
private lemma opposite_systems_conjugacy_theorem_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {F F'₁ F'₂ : Flag k V}
-- given
  (hyp : OppositeConjugacyCompositionHyp k V)
  (h₁ : Flag.isOppositeFlag F F'₁)
  (h₂ : Flag.isOppositeFlag F F'₂) :
-- imply
  ∃ (e : V ≃ₗ[k] V) (hlen : F'₁.len = F'₂.len), (∀ i : Fin F.len, (F.spaces i).map e.toLinearMap = F.spaces i) ∧ (∀ i : Fin F'₁.len, (F'₁.spaces i).map e.toLinearMap = F'₂.spaces (i.cast hlen)) := by
-- proof
  apply GeometricAlgebra.opposite_systems_conjugacy_theorem k V hyp F F'₁ F'₂ h₁ h₂


-- created on 2026-10-23
