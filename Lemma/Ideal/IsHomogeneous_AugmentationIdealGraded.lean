import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
Homogeneous of the graded augmentation ideal
Ideal.span (⋃ i > 0, 𝒮 i) (atlas ugmentationIdealGraded).

[isHomogeneous_augmentationIdealGraded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  [CommRing k]
  [CommRing S]
  [Algebra k S]
  {𝒮 : ℕ → Submodule k S}
  [GradedAlgebra 𝒮] :
-- imply
  Ideal.IsHomogeneous 𝒮 (Ideal.span (⋃ (i : ℕ) (_ : 0 < i), (𝒮 i : Set S))) := by
-- proof
  apply Ideal.homogeneous_span
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, _, hxi⟩ := hx
  exact ⟨i, hxi⟩


-- created on 2026-10-24
