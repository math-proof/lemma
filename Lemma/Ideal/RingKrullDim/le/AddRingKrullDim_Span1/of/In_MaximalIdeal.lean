import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[lemma_12_6_krull_dim_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  [CommRing A]
  [IsNoetherianRing A]
  [IsLocalRing A]
  {f : A}
-- given
  (hf : f ∈ IsLocalRing.maximalIdeal A) :
-- imply
  ringKrullDim A ≤ ringKrullDim (A ⧸ Ideal.span {f}) + 1 := by
-- proof
  have h : ({f} : Set A) ⊆ ↑(Ring.jacobson A) := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact Set.singleton_subset_iff.mpr hf
  have := ringKrullDim_le_ringKrullDim_quotient_add_encard {f} h
  simp [Set.encard_singleton] at this
  exact this


-- created on 2026-10-24
